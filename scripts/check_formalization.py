#!/usr/bin/env python3
"""Fail-closed checks for the current reviewed source set.

New modules or infrastructure changes need explicit allowlist review. These
checks do not establish mathematical relevance or replace human text review.
Only tracked project files are scanned; external packages are not project code.
Diagnostics intentionally do not echo rejected paths, text, or compiler output.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = ('Bridge01', 'Support01', 'Support02', 'Core02', 'Bridge02', 'Support03', 'Bridge03', 'Core03', 'Support04')
RESULTS = {'Bridge01': ('result01', 'result02', 'result03', 'result04'), 'Support01': ('result01', 'result02', 'result03', 'result04'), 'Support02': ('result01', 'result02', 'result03', 'result04', 'result05', 'result06', 'result07', 'result08', 'result09', 'result10', 'result11', 'result12', 'result13', 'result14', 'result15', 'result16', 'result17'), 'Core02': ('result01', 'result02', 'result03', 'result04', 'result05', 'result06', 'result07', 'result08', 'result09', 'result10', 'result11', 'result12', 'result13', 'result14', 'result15'), 'Bridge02': ('result01', 'result02', 'result03', 'result04', 'result05', 'result06', 'result07', 'result08', 'result09', 'result10', 'result11', 'result12', 'result13', 'result14', 'result15', 'result16', 'result17', 'result18', 'result19'), 'Support03': ('result16', 'result17', 'result18', 'result19', 'result20', 'result21', 'result22', 'result23', 'result24', 'result25', 'result26', 'result27'), 'Bridge03': ('result28', 'result29', 'result30', 'result31', 'result32', 'result33', 'result34', 'result35', 'result36', 'result37', 'result38', 'result39', 'result40', 'result41', 'result42', 'result43', 'result44', 'result45'), 'Core03': ('result46', 'result47', 'result48', 'result49', 'result50', 'result51', 'result52', 'result53', 'result54', 'result55', 'result56', 'result57', 'result58', 'result59', 'result60', 'result61', 'result62', 'result63'), 'Support04': ('result64', 'result65')}
OBJECTS = {'Bridge01': (), 'Support01': (), 'Support02': ('object01', 'object02', 'object03', 'object04', 'object05'), 'Core02': ('object01', 'object02', 'object03', 'object04'), 'Bridge02': ('object01', 'object02', 'object03', 'object04'), 'Support03': ('object05', 'object06'), 'Bridge03': ('object07', 'object08'), 'Core03': ('object09', 'object10', 'object11', 'object12'), 'Support04': ('object13', 'object14', 'object15')}
ABBREVIATIONS = {'Bridge01': (), 'Support01': (), 'Support02': (), 'Core02': ('type01', 'type02'), 'Bridge02': ('type01', 'type02', 'type03'), 'Support03': (), 'Bridge03': (), 'Core03': (), 'Support04': ()}
INSTANCES = {'Bridge01': (), 'Support01': (), 'Support02': (), 'Core02': ('inst01',), 'Bridge02': (), 'Support03': (), 'Bridge03': (), 'Core03': (), 'Support04': ()}
LEMMAS = {'Bridge01': (), 'Support01': (), 'Support02': (), 'Core02': (), 'Bridge02': ('result01', 'result02', 'result03', 'result04', 'result05', 'result06', 'result07', 'result08', 'result09', 'result10', 'result11', 'result12', 'result13', 'result14', 'result15', 'result16', 'result17', 'result18', 'result19'), 'Support03': (), 'Bridge03': (), 'Core03': (), 'Support04': ()}
NAMESPACES = {'Bridge01': 'Verification.Bridge01', 'Support01': 'Verification.Support01', 'Support02': 'Verification.Support02', 'Core02': 'Verification.Core02', 'Bridge02': 'Verification.Bridge02', 'Support03': 'Verification.Core02', 'Bridge03': 'Verification.Core02', 'Core03': 'Verification.Core02', 'Support04': 'Verification.Core02'}
IMPORTS = {'Bridge01': ('Mathlib',), 'Support01': ('Mathlib',), 'Support02': ('Mathlib',), 'Core02': ('Mathlib',), 'Bridge02': ('Mathlib', 'Verification.Core02'), 'Support03': ('Mathlib', 'Verification.Core02', 'Verification.Support02'), 'Bridge03': ('Mathlib', 'Verification.Core02', 'Verification.Bridge02', 'Verification.Support03'), 'Core03': ('Mathlib', 'Verification.Bridge03'), 'Support04': ('Mathlib', 'Verification.Core02')}
SCOPES = {'Bridge01': (), 'Support01': (), 'Support02': ('Scope01', 'Scope02', 'Scope03'), 'Core02': (), 'Bridge02': (), 'Support03': (), 'Bridge03': (), 'Core03': (), 'Support04': ()}
ALLOWED_PATHS = {
    ".github/workflows/lean.yml", ".gitignore", "README.md",
    "Verification.lean", "Verification/Basic.lean",
    "Verification/Bridge01.lean", "Verification/Support01.lean",
    "Verification/Support02.lean",
    "Verification/Core02.lean",
    "Verification/Bridge02.lean",
    "Verification/Support03.lean",
    "Verification/Bridge03.lean",
    "Verification/Core03.lean",
    "Verification/Support04.lean",
    "lakefile.toml", "lean-toolchain", "scripts/check_formalization.py",
}
# Digests freeze reviewed ancillary files and exact reviewed declaration modules.
FROZEN = {
    "Verification/Core02.lean": "7ef93ef4d0e95d48a444a24c05327c438a25776d5df1aa0e86cd21a6e245b5d0",
    "Verification/Bridge02.lean": "e211d6ba08f796b9f6226f4f122b21ab188c76ca9c491b527de5214c28f9b4ee",
    "Verification/Support03.lean": "96c65f8fe617d55fa71221ab6a839428fd61b8411d12ebee6f54dc488f7c0dac",
    "Verification/Bridge03.lean": "f21091baa8707c4bed3905cde2b41e66d5fab20a2cb7680d4390b45da68aa731",
    "Verification/Core03.lean": "acf907bb8dbec1bdce1e94063c36bd6a0cd75c2a8040e2b752750259b1db1b05",
    "Verification/Support04.lean": "c30669095cf8f30f985bc6f63768a2067aefcd4e77bfe67a57062e849bd3f9ed",
    "Verification/Support02.lean": "88de80f6e82021de839cac449cd5225deb383ec742f525e3b5f8e6d1dddb54c5",
    ".github/workflows/lean.yml": "3e735eafd883c9d2e51dac80f10d2b9429fb7280707be0c84889782ce9d5fed1",
    ".gitignore": "142c3492ed503a2267d84d699162b68169a8ad8661e1394fb235d4cd2746a757",
    "README.md": "887cf9e37f0ba3b6d90bac608ec581de79efdd632f8e8f3e0ae9219a72e7a425",
    "lakefile.toml": "3900f9a13cd03eb9d79f2d264c3134a54d1c1c080ea61d42c309c940cb4f063d",
    "lean-toolchain": "d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b",
    "Verification/Basic.lean": "4c7d76a39643d8e1d302a3a9f043f5623b6ae8585cd6c45a959c76ea23d61e56",
}
MATHLIB_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BLOCKED_LEAN = {
    "sorry", "admit", "sorryAx", "axiom", "constant", "unsafe",
    "implemented_by", "run_tac", "run_elab", "run_cmd", "elab", "macro", "syntax",
    "initialize", "builtin_initialize", "opaque", "def", "abbrev", "alias",
    "export", "instance", "inductive", "structure", "class", "set_option",
}
# Generic metadata signatures, with no source-specific names or titles.
RESTRICTED_TAG = bytes((78, 76, 83)).decode("ascii").casefold()
METADATA = re.compile(
    r"\b(?:manu" r"script|submis" r"sion|submit" r"ted|ar" r"xiv|"
    r"d" r"oi|or" r"cid|affili" r"ation|corresponding\s+author)\b|"
    r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}|"
    r"\b(?:ti" r"tle|au" r"thors?|jour" r"nal)\s*[:=]", re.IGNORECASE,
)


class GateError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise GateError(message)


def active_lean(source):
    """Remove nested comments and strings without joining adjacent tokens."""
    result = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result[i:i + 2] = "  "
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
                continue
            if source[i] != "\n":
                result[i] = " "
        elif quoted:
            if source[i] == "\\":
                result[i:i + 2] = " " * len(source[i:i + 2])
                i += 2
                continue
            if source[i] == '"':
                quoted = False
            if source[i] != "\n":
                result[i] = " "
        elif pair == "/-":
            depth = 1
            result[i:i + 2] = "  "
            i += 2
            continue
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
            continue
        elif source[i] == '"':
            quoted = True
            result[i] = " "
        i += 1
    require(not depth and not quoted, "Unterminated Lean comment or string")
    return "".join(result)


def check_tokens(source, reviewed_definitions=(), reviewed_abbreviations=(), reviewed_instances=()):
    active = active_lean(source)
    if reviewed_definitions:
        require(re.findall(r"\bdef\s+(\S+)", active) == list(reviewed_definitions),
                "Definition name allowlist mismatch")
        active = re.sub(r"(?m)^def (?=object[0-9]{2}\s)", "", active)
    if reviewed_abbreviations:
        require(re.findall(r"\babbrev\s+(\S+)", active) == list(reviewed_abbreviations),
                "Abbreviation name allowlist mismatch")
        active = re.sub(r"(?m)^abbrev (?=type[0-9]{2}\s)", "", active)
    if reviewed_instances:
        require(re.findall(r"\binstance\s+(\S+)", active) == list(reviewed_instances),
                "Instance name allowlist mismatch")
        active = re.sub(r"(?m)^local instance (?=inst[0-9]{2}\s)", "", active)
    tokens = set(re.findall(r"[^\W\d]\w*", active))
    require(not tokens.intersection(BLOCKED_LEAN), "Disallowed active Lean token")


def check_metadata(source):
    require(RESTRICTED_TAG not in source.casefold(), "Restricted text signature")
    require(not METADATA.search(source), "Unreviewed metadata signature")
    require("\x00" not in source, "Binary content is not permitted")


def check_paths(entries):
    require(set(entries) == ALLOWED_PATHS, "Tracked path allowlist mismatch")
    require(all(mode == "100644" for mode in entries.values()),
            "Only regular non-executable tracked files are permitted")


def check_lean(path, source):
    # Every declaration exception is bound to the complete reviewed bytes.
    definitions, abbreviations, instances = (), (), ()
    module = Path(path).stem
    if path in FROZEN and module in MODULES:
        require(hashlib.sha256(source.encode("utf-8")).hexdigest() == FROZEN[path],
                "Reviewed declaration module changed")
        definitions = OBJECTS[module]
        abbreviations = ABBREVIATIONS[module]
        instances = INSTANCES[module]
    check_tokens(source, definitions, abbreviations, instances)
    active = active_lean(source)
    require(active == source, "Lean comments and strings need separate review")
    require("«" not in active and "»" not in active, "Quoted identifiers are not permitted")
    if path == "Verification.lean":
        expected = "".join(f"import Verification.{m}\n" for m in ("Basic",) + MODULES)
        require(source == expected, "Root module must import the complete reviewed set")
        return
    expected_imports = ("Mathlib",) if module == "Basic" else IMPORTS[module]
    require(re.findall(r"(?m)^[ \t]*import\s+(\S+)\s*$", active) == list(expected_imports)
            and len(re.findall(r"\bimport\b", active)) == len(expected_imports),
            "Module import allowlist mismatch")
    if path == "Verification/Basic.lean":
        return  # Its complete contents are frozen above.
    module = Path(path).stem
    namespace = NAMESPACES[module]
    require(re.findall(r"(?m)^[ \t]*namespace\s+(\S+)\s*$", active) == [namespace]
            and len(re.findall(r"\bnamespace\b", active)) == 1,
            "Namespace allowlist mismatch")
    require(re.findall(r"(?m)^[ \t]*end\s+(\S+)\s*$", active)
            == list(SCOPES[module]) + [namespace]
            and len(re.findall(r"\bend\b", active)) == len(SCOPES[module]) + 1,
            "Namespace closing mismatch")
    expected_results = [("lemma" if name in LEMMAS[module] else "theorem", name)
                        for name in RESULTS[module]]
    require(re.findall(r"\b(theorem|lemma)\s+(\S+)", active) == expected_results,
            "Theorem kind and name allowlist mismatch")
    require(not re.search(r"\bexample\b", active), "Unexpected declaration")
    expected_prints = [f"#print axioms {namespace}.{name}"
                       for name in RESULTS[module] + OBJECTS[module] + ABBREVIATIONS[module] + INSTANCES[module]]
    require(re.findall(r"(?m)^[ \t]*#.*$", active) == expected_prints
            and active.count("#") == len(expected_prints),
            "Command allowlist mismatch")


def check_sources():
    proc = subprocess.run(["git", "ls-files", "--stage", "-z"], cwd=ROOT,
                          check=True, capture_output=True)
    entries = {}
    for record in proc.stdout.decode("utf-8").split("\0"):
        if record:
            info, path = record.split("\t", 1)
            mode, _, stage = info.split()
            require(stage == "0", "Unmerged tracked file")
            entries[path] = mode
    check_paths(entries)  # Reject paths before opening files or invoking Lean.
    clean = subprocess.run(["git", "diff", "--quiet", "--exit-code"], cwd=ROOT)
    require(clean.returncode == 0, "Tracked working tree differs from the index")
    for path in sorted(entries):
        file = ROOT / path
        require(not file.is_symlink(), "Symbolic links are not permitted")
        data = file.read_bytes()
        source = data.decode("utf-8")
        check_metadata(source)
        if path in FROZEN:
            require(hashlib.sha256(data).hexdigest() == FROZEN[path],
                    "Reviewed ancillary content changed")
        if path.endswith(".lean"):
            check_lean(path, source)
    print("Tracked source gate passed")


def check_dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    require(len(packages) == 1 and packages[0]["rev"] == MATHLIB_REV,
            "Resolved dependency revision differs from the reviewed revision")
    print("Dependency revision gate passed")


def parse_axioms(output, expected):
    records = re.findall(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|"
        r"(does not depend on any axioms))", output,
    )
    require(len(records) == len(expected), "Incomplete axiom-check output")
    require({name for name, _, _ in records} == set(expected),
            "Axiom-check theorem set mismatch")
    for _, values, _ in records:
        dependencies = {v.strip() for v in values.split(",") if v.strip()}
        require(dependencies <= ALLOWED_AXIOMS, "Unapproved theorem axiom dependency")


def check_axioms():
    for module in MODULES:
        proc = subprocess.run(["lake", "env", "lean", f"Verification/{module}.lean"],
                              cwd=ROOT, capture_output=True, text=True)
        require(proc.returncode == 0, "Theorem axiom-check compilation failed")
        parse_axioms(proc.stdout + proc.stderr,
                     [f"{NAMESPACES[module]}.{name}"
                      for name in RESULTS[module] + OBJECTS[module] + ABBREVIATIONS[module] + INSTANCES[module]])
    print("All reviewed declaration axiom checks passed")


def self_test():
    def rejects(fn, *args):
        try:
            fn(*args)
        except GateError:
            return
        raise GateError("Gate rejection self-test failed")

    for token in BLOCKED_LEAN:
        rejects(check_tokens, f"theorem result01 : True := {token}")
    check_tokens('-- sorry\n/- admit /- sorryAx -/ axiom -/\n"sorry"\nby simp')
    check_tokens("by simp\n  exact admitResult")
    rejects(active_lean, "/- unfinished")
    rejects(check_metadata, RESTRICTED_TAG)
    rejects(check_metadata, "submis" "sion")
    valid = dict.fromkeys(ALLOWED_PATHS, "100644")
    check_paths(valid)
    for suffix in (".tex", ".pdf", ".lean"):
        rejects(check_paths, valid | {"Unreviewed" + suffix: "100644"})
    rejects(check_paths, valid | {"Verification/Bridge01.lean": "120000"})
    rejects(check_paths, {p: m for p, m in valid.items() if p != "Verification.lean"})
    rejects(check_lean, "Verification.lean", "import Verification.Basic\n")
    sample = "import Mathlib\nnamespace Verification.Bridge01\n" + "\n".join(
        f"theorem {name} : True := by trivial" for name in RESULTS["Bridge01"]
    ) + "\n" + "\n".join(
        f"#print axioms Verification.Bridge01.{name}" for name in RESULTS["Bridge01"]
    ) + "\nend Verification.Bridge01\n"
    check_lean("Verification/Bridge01.lean", sample)
    for addition in ('open Nat in #eval 1', ' import Init', '-- note',
                     '"note"', '«note»', ' namespace Other'):
        rejects(check_lean, "Verification/Bridge01.lean", sample + addition + "\n")
    reviewed = (ROOT / "Verification/Support02.lean").read_text()
    check_lean("Verification/Support02.lean", reviewed)
    for addition in ("\ndef object06 : Nat := 0\n", "\naxiom result18 : False\n",
                     "\n-- note\n", "\n#print axioms Nat.add_comm\n"):
        rejects(check_lean, "Verification/Support02.lean", reviewed + addition)
    rejects(check_lean, "Verification/Support02.lean",
            reviewed.replace("result17", "result18"))
    rejects(check_lean, "Verification/Support02.lean",
            reviewed.replace("object05", "object06"))
    rejects(check_lean, "Verification/Bridge01.lean", sample + "\ndef object01 : Nat := 0\n")
    for module in MODULES:
        path = f"Verification/{module}.lean"
        if path not in FROZEN:
            continue
        reviewed = (ROOT / path).read_text()
        check_lean(path, reviewed)
        for addition in ("\ndef object99 : Nat := 0\n", "\nabbrev type99 := Nat\n",
                         "\nlocal instance inst99 : Fact True := ⟨by trivial⟩\n",
                         "\nlemma result99 : True := by trivial\n", "\naxiom result99 : False\n",
                         "\n-- note\n", "\n#print axioms Nat.add_comm\n", "\nimport Init\n"):
            rejects(check_lean, path, reviewed + addition)
        rejects(check_lean, path, reviewed.replace(RESULTS[module][0], "result99"))
    rejects(check_tokens, "abbrev type01 := Nat")
    rejects(check_tokens, "local instance inst01 : Fact True := ⟨by trivial⟩")
    rejects(check_tokens, "def object01 : Nat := 0", ("object02",))
    rejects(check_tokens, "abbrev type01 := Nat", (), ("type02",))
    rejects(check_tokens, "local instance inst01 : Fact True := ⟨by trivial⟩", (), (), ("inst02",))
    parse_axioms("'Verification.Bridge01.result01' depends on axioms: "
                 "[propext, Classical.choice, Quot.sound]", ["Verification.Bridge01.result01"])
    parse_axioms("'Verification.Support01.result03' does not depend on any axioms",
                 ["Verification.Support01.result03"])
    rejects(parse_axioms, "'x' depends on axioms: [sorryAx]", ["x"])
    rejects(parse_axioms, "'x' depends on axioms: [Other.result01]", ["x"])
    rejects(parse_axioms, "", ["x"])
    rejects(parse_axioms, "'x' depends on axioms: [propext]", ["y"])
    rejects(parse_axioms, "'x' depends on axioms: [propext]\n" * 2, ["x", "y"])
    print("Formalization gate self-tests passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    for option in ("sources", "dependencies", "axioms", "self-test"):
        group.add_argument("--" + option, action="store_true")
    args = parser.parse_args()
    try:
        if args.sources:
            check_sources()
        elif args.dependencies:
            check_dependencies()
        elif args.axioms:
            check_axioms()
        else:
            self_test()
    except GateError as error:
        print(f"Formalization gate failed: {error}", file=sys.stderr)
        return 1
    except (OSError, UnicodeError, ValueError, KeyError,
            subprocess.SubprocessError):
        print("Formalization gate failed; review locally without exposing rejected content",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
