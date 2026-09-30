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
MODULES = ("Bridge01", "Support01")
RESULTS = tuple(f"result{i:02}" for i in range(1, 5))
ALLOWED_PATHS = {
    ".github/workflows/lean.yml", ".gitignore", "README.md",
    "Verification.lean", "Verification/Basic.lean",
    "Verification/Bridge01.lean", "Verification/Support01.lean",
    "lakefile.toml", "lean-toolchain", "scripts/check_formalization.py",
}
# Digests freeze the already reviewed neutral ancillary files.
FROZEN = {
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


def check_tokens(source):
    tokens = set(re.findall(r"[^\W\d]\w*", active_lean(source)))
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
    check_tokens(source)
    active = active_lean(source)
    require(active == source, "Lean comments and strings need separate review")
    require("«" not in active and "»" not in active, "Quoted identifiers are not permitted")
    if path == "Verification.lean":
        expected = "".join(f"import Verification.{m}\n" for m in ("Basic",) + MODULES)
        require(source == expected, "Root module must import the complete reviewed set")
        return
    require(re.findall(r"(?m)^[ \t]*import\s+(\S+)\s*$", active) == ["Mathlib"]
            and len(re.findall(r"\bimport\b", active)) == 1,
            "Module import allowlist mismatch")
    if path == "Verification/Basic.lean":
        return  # Its complete contents are frozen above.
    module = Path(path).stem
    namespace = f"Verification.{module}"
    require(re.findall(r"(?m)^[ \t]*namespace\s+(\S+)\s*$", active) == [namespace]
            and len(re.findall(r"\bnamespace\b", active)) == 1,
            "Namespace allowlist mismatch")
    require(re.findall(r"(?m)^[ \t]*end\s+(\S+)\s*$", active) == [namespace]
            and len(re.findall(r"\bend\b", active)) == 1,
            "Namespace closing mismatch")
    require(re.findall(r"\btheorem\s+(\S+)", active) == list(RESULTS),
            "Theorem name allowlist mismatch")
    require(not re.search(r"\b(?:lemma|example)\b", active), "Unexpected declaration")
    expected_prints = [f"#print axioms {namespace}.{name}" for name in RESULTS]
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
                     [f"Verification.{module}.{name}" for name in RESULTS])
    print("All eight theorem axiom checks passed")


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
        f"theorem {name} : True := by trivial" for name in RESULTS
    ) + "\n" + "\n".join(
        f"#print axioms Verification.Bridge01.{name}" for name in RESULTS
    ) + "\nend Verification.Bridge01\n"
    check_lean("Verification/Bridge01.lean", sample)
    for addition in ('open Nat in #eval 1', ' import Init', '-- note',
                     '"note"', '«note»', ' namespace Other'):
        rejects(check_lean, "Verification/Bridge01.lean", sample + addition + "\n")
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
