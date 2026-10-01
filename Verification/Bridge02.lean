import Mathlib
import Verification.Core02

open MeasureTheory FourierTransform
open scoped ENNReal Convolution SchwartzMap
noncomputable section
namespace Verification.Bridge02
abbrev type01 := Verification.Core02.type01
abbrev type02 := Lp ℂ 2 (volume : Measure type01)
abbrev type03 := Lp ℂ ⊤ (volume : Measure type01)
def object01 (m : type03) : type02 →L[ℂ] type02 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 m
lemma result01 (m : type03) (f : type02) :
    object01 m f =ᵐ[volume] fun x => m x * f x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder m f
lemma result02 (m : type03) (f : type02) : ‖object01 m f‖ ≤ ‖m‖ * ‖f‖ := by
  have h : object01 m f = (m • f : type02) := by
    apply Lp.ext
    filter_upwards [result01 m f, Lp.coeFn_lpSMul (r := 2) m f] with x hm hs
    simpa [hm] using hs.symm
  rw [h]
  exact Lp.norm_smul_le m f

def object02 (m : type03) : type02 →L[ℂ] type02 :=
  fourierInvCLM ℂ type02 ∘L object01 m ∘L fourierCLM ℂ type02

lemma result03 {f : type01 → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2) (hF2 : MemLp (𝓕 f) 2) :
    𝓕 hf2.toLp = hF2.toLp := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕 hf2.toLp) = Lp.toTemperedDistribution hF2.toLp
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, (𝓕 g) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      simp [hx]
    _ = ∫ x, g x * 𝓕 f x := by
      simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral, real_inner_comm] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ type01) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner (g.integrable (μ := volume)) hf)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF2.coeFn_toLp] with x hx
      simp [hx]

lemma result04 {k : type01 → ℂ} (hk : Integrable k) : MemLp (𝓕 k) ⊤ := by
  refine memLp_top_of_bound ?_ (∫ x, ‖k x‖) ?_
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ type01) continuous_inner hk).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.fourier_eq]
    simpa only [Circle.norm_smul] using
      norm_integral_le_integral_norm (fun x => Real.fourierChar (-inner ℝ x ξ) • k x)

def object03 {k : type01 → ℂ} (hk : Integrable k) : type03 := (result04 hk).toLp

lemma result05 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ)) :
    MemLp (𝓕 (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g)) 2 := by
  have h : MemLp (fun ξ => 𝓕 k ξ * (𝓕 g) ξ) 2 :=
    (result04 hk).mul ((𝓕 g).memLp 2 volume)
  refine MemLp.ae_eq ?_ h
  filter_upwards with ξ
  rw [Real.fourier_mul_convolution_eq hk (g.integrable (μ := volume))]
  rfl

lemma result06 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ))
    (hc : MemLp (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2) :
    𝓕 hc.toLp = object01 (object03 hk) (𝓕 (g.toLp 2)) := by
  rw [result03 (hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (g.integrable (μ := volume))) hc (result05 hk g),
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(result05 hk g).coeFn_toLp,
    result01 (object03 hk) ((𝓕 g).toLp 2),
    (result04 hk).coeFn_toLp, (𝓕 g).coeFn_toLp 2 volume] with ξ hc hm hkval hg
  rw [hc, hm, hg]
  change 𝓕 (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ =
    ((result04 hk).toLp : type01 → ℂ) ξ * (𝓕 g) ξ
  rw [hkval, Real.fourier_mul_convolution_eq]
  · rfl
  · exact hk
  · exact g.integrable

lemma result07 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ))
    (hc : MemLp (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2) :
    object02 (object03 hk) (g.toLp 2) = hc.toLp := by
  change 𝓕⁻ (object01 (object03 hk) (𝓕 (g.toLp 2))) = hc.toLp
  rw [← result06 hk g hc, fourierInv_fourier_eq]

lemma result08 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ)) :
    MemLp (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2 := by
  let C := SchwartzMap.seminorm ℝ 0 0 g
  let B := (∫ z, ‖k z‖) * C
  have h1 := hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (g.integrable (μ := volume))
  have hb (x : type01) : ‖(k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ ≤ B := by
    calc
      _ ≤ ∫ z, ‖k z * g (x-z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ‖k z‖ * C := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
        · exact hk.norm.mul_const C
        · filter_upwards with z
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g (x-z)) (norm_nonneg _)
      _ = B := integral_mul_const C _
  apply (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mpr
  apply (h1.norm.const_mul B).mono' (h1.aestronglyMeasurable.norm.pow 2)
  filter_upwards with x
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm, pow_two, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right (hb x) (norm_nonneg ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x))

lemma result09 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ)) :
    object02 (object03 hk) (g.toLp 2) =
      (result08 hk g).toLp :=
  result07 hk g (result08 hk g)

def object04 (h : 𝓢(type01, ℂ)) : type02 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ h) ∘L
    Lp.toTemperedDistributionCLM ℂ volume 2

lemma result10 (h : 𝓢(type01, ℂ)) (f : type02) :
    object04 h f = Lp.toTemperedDistribution f h := rfl

lemma result11 (h : 𝓢(type01, ℂ)) (f : type02) :
    object04 h f = ∫ x, h x * f x := by
  change Lp.toTemperedDistribution f h = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]

lemma result12 (h g : 𝓢(type01, ℂ)) (z : type01) :
    object04 h (Verification.Core02.object01 z (g.toLp 2)) = ∫ x, h x * g (x-z) := by
  rw [result11]
  apply integral_congr_ae
  have hg := (measurePreserving_sub_right (volume : Measure type01) z).quasiMeasurePreserving.ae_eq_comp
    (g.coeFn_toLp 2 volume)
  filter_upwards [Verification.Core02.result02 z (g.toLp 2), hg] with x hx hgx
  simpa only [Function.comp_apply, hx] using congrArg (h x * ·) hgx

lemma result13 {k : type01 → ℂ} (hk : Integrable k) (g : 𝓢(type01, ℂ)) :
    Verification.Core02.object02 k (g.toLp 2) = (result08 hk g).toLp := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
  ext h
  rw [← result10, ← result10]
  have hi : Integrable (fun p : type01 × type01 => h p.1 * (k p.2 * g (p.1 - p.2)))
      (volume.prod volume) :=
    (hk.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) (g.integrable (μ := volume))).bdd_mul
      (h.continuous.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => SchwartzMap.norm_le_seminorm ℝ h p.1)
  calc
    _ = ∫ z, k z * object04 h (Verification.Core02.object01 z (g.toLp 2)) := by
      rw [Verification.Core02.object02]
      rw [← (object04 h).integral_comp_comm (μ := volume)
        (φ := fun z : type01 => k z • Verification.Core02.object01 z (g.toLp 2 volume))
        (Verification.Core02.result06 hk (g.toLp 2 volume))]
      simp only [map_smul, smul_eq_mul]
    _ = ∫ z, ∫ x, h x * (k z * g (x-z)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [result12, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ x, ∫ z, h x * (k z * g (x-z)) := integral_integral_swap hi.swap
    _ = ∫ x, h x * (k ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_const_mul]
      rfl
    _ = _ := by
      rw [result11]
      apply integral_congr_ae
      filter_upwards [(result08 hk g).coeFn_toLp] with x hx
      rw [hx]

lemma result14 {k : type01 → ℂ} (hk : Integrable k)
    (g : 𝓢(type01, ℂ)) :
    Verification.Core02.object02 k (g.toLp 2) = object02 (object03 hk) (g.toLp 2) := by
  rw [result13 hk g, result09 hk g]

lemma result15 {k : type01 → ℂ} (hk : Integrable k) :
    Verification.Core02.object03 k hk = object02 (object03 hk) := by
  apply DFunLike.coe_injective
  apply (SchwartzMap.denseRange_toLpCLM (E := type01) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).equalizer
    (Verification.Core02.object03 k hk).continuous
    (object02 (object03 hk)).continuous
  funext g
  exact result14 hk g

lemma result16 {k : type01 → ℂ} (hk : Integrable k) (f : type02) :
    Verification.Core02.object02 k f = object02 (object03 hk) f := by
  exact congrArg (fun T : type02 →L[ℂ] type02 => T f) (result15 hk)

lemma result17 {k : type01 → ℂ} (hk : Integrable k) :
    object03 hk =ᵐ[volume] 𝓕 k := (result04 hk).coeFn_toLp

lemma result18 {k : type01 → ℂ} (hk : Integrable k) (f : type02) :
    𝓕 (Verification.Core02.object02 k f) = object01 (object03 hk) (𝓕 f) := by
  rw [result16 hk f]
  change 𝓕 (𝓕⁻ (object01 (object03 hk) (𝓕 f))) = _
  exact fourier_fourierInv_eq _

lemma result19 {k : type01 → ℂ} (hk : Integrable k) (f : type02) :
    𝓕 (Verification.Core02.object02 k f) =ᵐ[volume] fun ξ => 𝓕 k ξ * (𝓕 f) ξ := by
  rw [result18 hk f]
  filter_upwards [result01 (object03 hk) (𝓕 f), result17 hk] with ξ hm hkξ
  rw [hm, hkξ]

#print axioms Verification.Bridge02.result01
#print axioms Verification.Bridge02.result02
#print axioms Verification.Bridge02.result03
#print axioms Verification.Bridge02.result04
#print axioms Verification.Bridge02.result05
#print axioms Verification.Bridge02.result06
#print axioms Verification.Bridge02.result07
#print axioms Verification.Bridge02.result08
#print axioms Verification.Bridge02.result09
#print axioms Verification.Bridge02.result10
#print axioms Verification.Bridge02.result11
#print axioms Verification.Bridge02.result12
#print axioms Verification.Bridge02.result13
#print axioms Verification.Bridge02.result14
#print axioms Verification.Bridge02.result15
#print axioms Verification.Bridge02.result16
#print axioms Verification.Bridge02.result17
#print axioms Verification.Bridge02.result18
#print axioms Verification.Bridge02.result19
#print axioms Verification.Bridge02.object01
#print axioms Verification.Bridge02.object02
#print axioms Verification.Bridge02.object03
#print axioms Verification.Bridge02.object04
#print axioms Verification.Bridge02.type01
#print axioms Verification.Bridge02.type02
#print axioms Verification.Bridge02.type03

end Verification.Bridge02
