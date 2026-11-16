#!/usr/bin/env python3
"""2024/2025 official SHED recontact microdata analysis; outputs aggregates only.
No respondent-level observations are copied into GitHub or artifact outputs.
"""
import hashlib
import json
import urllib.request
import zipfile
from pathlib import Path
import numpy as np
import pandas as pd
import statsmodels.formula.api as smf

OUT=Path("shed_results")
OUT.mkdir(exist_ok=True)
URL="https://www.federalreserve.gov/consumerscommunities/files/SHED_public_use_data_{}_%28CSV%29.zip"
EXPECTED={2024:{"N":12295,"E2":2937,"E2B":2000,"I0_f":2721,"EF1":7151},
          2025:{"N":12934,"E2":2860,"E2B":2342,"I0_f":2694,"EF1":7327}}
MISSING=[-1,-2,-3,-7,-8,-9,-99]
def normalize_binary(raw,name):
    v=raw.astype("string").str.strip().str.lower()
    mapped=v.map({"yes":1.0,"no":0.0,"1":1.0,"0":0.0,"1.0":1.0,"0.0":0.0})
    allowed={"yes","no","1","0","1.0","0.0","-1","-2","-3","-7","-8","-9","-99",
             "don't know","refused","not asked","missing"}
    unexpected=v.notna() & (~v.isin(list(allowed)))
    if unexpected.any():
        raise RuntimeError(f"{name}: unrecognized categorical codes {v[unexpected].value_counts().head().to_dict()}")
    return mapped.astype(float)

def get(year):
    url=URL.format(year)
    dest=Path(f"/tmp/SHED_{year}.zip")
    req=urllib.request.Request(url,headers={"User-Agent":"Mozilla/5.0 SHED-public-use-academic-analysis"})
    with urllib.request.urlopen(req,timeout=120) as source, dest.open("wb") as target:
        while data:=source.read(1024*1024):
            target.write(data)
    if not zipfile.is_zipfile(dest):
        raise RuntimeError(f"{year}: response is not ZIP")
    with zipfile.ZipFile(dest) as z:
        if z.testzip() is not None:
            raise RuntimeError(f"{year}: corrupt ZIP")
        files=[x for x in z.infolist() if x.filename.lower().endswith(".csv")]
        if not files: raise RuntimeError(f"{year}: missing CSV")
        x=max(files,key=lambda e:e.file_size)
        with z.open(x) as f:
            d=pd.read_csv(f,low_memory=False,dtype={"shedid":"string"})
        member=x.filename
    d.columns=[str(c).strip().lstrip("\ufeff") for c in d.columns]
    d=d.rename(columns={c:c.lower() for c in d.columns if c.lower() in ["shedid","panel_weight"]})
    if len(d)!=EXPECTED[year]["N"]:raise RuntimeError(f"{year}: unexpected N={len(d)}")
    if "shedid" not in d or d.shedid.isna().any() or d.shedid.duplicated().any():
        raise RuntimeError(f"{year}: broken respondent identifier")
    lookup={str(k).lower():k for k in d}
    for key,val in EXPECTED[year].items():
        if key=="N":continue
        if key.lower() not in lookup:raise RuntimeError(f"{year}: missing {key}")
        raw=d[lookup[key.lower()]]
        b=normalize_binary(raw,f"{year}:{key}")
        print("CODING_CHECK",year,key,"raw",raw.value_counts(dropna=False).head(10).to_dict(),"coded",b.value_counts(dropna=False).head(10).to_dict(),flush=True)
        if not b.dropna().isin([0,1,*MISSING]).all():
            raise RuntimeError(f"{year}: nonbinary coding {key}")
        got=int(b.eq(1).sum())
        if got!=val:raise RuntimeError(f"{year}: official count mismatch for {key}: {got}!={val}")
    provenance={"year":year,"url":url,"member":member,"zip_bytes":dest.stat().st_size,
                "sha256":hashlib.sha256(dest.read_bytes()).hexdigest(),
                "n":len(d),"ncolumns":len(d.columns)}
    print("SOURCE VERIFIED",json.dumps(provenance))
    return d,provenance

def col(d,k):
    candidates={x.lower():x for x in d}
    if k.lower() not in candidates: raise RuntimeError(f"missing {k}")
    return d[candidates[k.lower()]]
def binary(d,k):
    return normalize_binary(col(d,k),k)
def category(d,k,low,high):
    raw=col(d,k)
    print("CATEGORY_CHECK",k,raw.value_counts(dropna=False).head(12).to_dict(),flush=True)
    numeric=pd.to_numeric(raw,errors="coerce")
    if numeric.notna().mean()>0.8:
        numeric=numeric.replace(MISSING,np.nan)
        if not numeric.dropna().between(low,high).all():
            raise RuntimeError(f"bad category {k}: {numeric.dropna().unique()[:10]}")
        return numeric.astype(float)
    v=raw.astype("string").str.strip()
    v=v.mask(v.str.lower().isin(["don't know","refused","prefer not to answer","not answered","-2","-1","nan"]),pd.NA)
    if v.dropna().nunique()>high-low+1:
        print("CATEGORY_WARN",k,"more than expected levels",v.value_counts(dropna=False).head(12).to_dict())
    return v.astype(object)
d24,src24=get(2024)
d25,src25=get(2025)
b24=pd.DataFrame({"shedid":col(d24,"shedid").astype("string").str.strip()})
for k in ["E2","E2B","I0_f","I0_c","EF1","E4_c"]:
    b24[k]=binary(d24,k)
for k,lo,hi in [("ppage",18,120),("ppgender",1,2),("ppeduc5",1,5),("ppinc7",1,7),("ppreg4",1,4)]:
    b24[k]=category(d24,k,lo,hi)
b25=pd.DataFrame({"shedid":col(d25,"shedid").astype("string").str.strip()})
for k in ["E2","E2B"]:
    b25[k]=binary(d25,k)
b25["panel_weight"]=pd.to_numeric(col(d25,"panel_weight"),errors="coerce")
if (b25.panel_weight>0).sum()!=4419:
    raise RuntimeError(f"panel weights: {(b25.panel_weight>0).sum()} rather than 4419")
matched=b24.merge(b25,on="shedid",validate="one_to_one",suffixes=("_24","_25"))
p=matched[matched.panel_weight.gt(0)].copy()
if len(p)!=4419:
    raise RuntimeError(f"positive-weight matched IDs {len(p)} != 4419")
age=p[p.ppage>=50].copy()
base=age[(age.E2_24==0)&(age.E2B_24==0)].copy()
nodebt=age[age.E2B_24==0].copy()
flow={"n_2024":len(d24),"n_2025":len(d25),"matched_ids":len(matched),
      "positive_weight_matched":len(p),"age50_plus":len(age),
      "no_baseline_medical_debt":len(nodebt),"strict_no_debt_no_shock":len(base)}
def prep(x):
    z=x.copy()
    z["Y"]=z.E2B_25
    z["S"]=z.E2_25
    z["P"]=z.I0_f
    z["L"]=1-z.EF1
    z["SS"]=z.I0_c
    z["insurance"]=z.E4_c
    z["age_c"]=z.ppage-60
    z["gender"]=z.ppgender
    z["education"]=z.ppeduc5
    z["income"]=z.ppinc7
    z["region"]=z.ppreg4
    z["S_prior"]=z.E2_24
    z["Y_prior"]=z.E2B_24
    cols=["Y","S","P","L","SS","insurance","age_c","gender","education","income",
          "region","S_prior","Y_prior","panel_weight"]
    return z.dropna(subset=cols)
base=prep(base); nodebt=prep(nodebt); age=prep(age)
flow.update(strict_complete_cases=len(base),no_debt_complete_cases=len(nodebt),
            all_age50_complete_cases=len(age))
def cells(df,names):
    import itertools
    g=df.groupby(names).size().to_dict()
    return {"/".join(map(str,cs)):int(g.get(cs,0)) for cs in itertools.product([0.,1.],repeat=len(names))}
COV="age_c+I(age_c**2)+C(gender)+C(education)+C(income)+C(region)+insurance+SS"
FMT={"main":"Y ~ S*P+L+"+COV,
     "triple":"Y ~ S*P*L+"+COV,
     "social_security":"Y ~ S*SS+P+L+age_c+I(age_c**2)+C(gender)+C(education)+C(income)+C(region)+insurance",
     "no_baseline_debt":"Y ~ S*P+L+S_prior+"+COV,
     "all_age50":"Y ~ S*P+L+S_prior+Y_prior+"+COV,
     "unweighted":"Y ~ S*P+L+"+COV}
fits={}
coef=[]
def model(name,df,group,minimum,unweighted=False):
    cc=cells(df,group)
    out={"n":len(df),"cells":cc,"model":name,"weight_type":"unweighted" if unweighted else "2025_panel_weight",
         "formula":FMT[name],"covariance":"HC3","status":"NOT_ESTIMABLE"}
    if len(df)<80 or min(cc.values())<minimum:
        out["reason"]=f"n<80 or some cell count<{minimum}";return out
    w=pd.Series(1.,index=df.index) if unweighted else df.panel_weight
    m=smf.wls(FMT[name],data=df,weights=w)
    if np.linalg.matrix_rank(m.exog)!=m.exog.shape[1]:
        out["reason"]="rank-deficient regression design";return out
    result=m.fit(cov_type="HC3")
    out["status"]="OK"
    out["weighted_effective_n"]=float(w.sum()**2/(w*w).sum())
    ci=result.conf_int()
    for term in result.params.index:
        coef.append({"model":name,"term":term,"estimate":float(result.params[term]),
                     "se_HC3":float(result.bse[term]),"p_value":float(result.pvalues[term]),
                     "ci_low":float(ci.loc[term,0]),"ci_high":float(ci.loc[term,1]),"n":int(len(df))})
    print("MODEL",name,"N",len(df),"INTERACTION",
          {k:round(float(result.params[k]),6) for k in result.params.index if ":" in k})
    return out
fits["main"]=model("main",base,["S","P"],12)
fits["triple"]=model("triple",base,["S","P","L"],20)
fits["social_security"]=model("social_security",base,["S","SS"],12)
fits["no_baseline_debt"]=model("no_baseline_debt",nodebt,["S","P"],12)
fits["all_age50"]=model("all_age50",age,["S","P"],12)
fits["unweighted"]=model("unweighted",base,["S","P"],12,True)
groups=[]
for s in (0.,1.):
    for pt in (0.,1.):
        z=base[(base.S==s)&(base.P==pt)]
        n=len(z)
        groups.append({"S":int(s),"P":int(pt),"n":n,
                       "weighted_y_rate":float(np.average(z.Y,weights=z.panel_weight)) if n else None,
                       "unweighted_y_rate":float(z.Y.mean()) if n else None})
summary={"provenance":[src24,src25],"sample_flow":flow,"models":fits,
         "key_coefs":[x for x in coef if x["term"] in ["S","P","S:P","L","S:SS","S:P:L"]],
         "group_rates":groups,
         "warnings":["SHED is a survey of adults, not an independently sampled household panel",
                     "E2 and E2B both measured in 2025; concurrent association, not temporal causation",
                     "HC3 WLS does not implement full complex-survey variance estimation",
                     "2024/2025 national CPI cannot identify a respondent-level causal inflation effect",
                     "Survey recontact attrition and selection not fully identified"]}
(OUT/"summary.json").write_text(json.dumps(summary,indent=2))
pd.DataFrame(coef).to_csv(OUT/"coefficients.csv",index=False)
pd.DataFrame(groups).to_csv(OUT/"group_rates.csv",index=False)
pd.DataFrame([{"step":k,"n":v} for k,v in flow.items()]).to_csv(OUT/"sample_flow.csv",index=False)
print("RESULTS_JSON_BEGIN")
print(json.dumps(summary,indent=2))
print("RESULTS_JSON_END")
