#!/usr/bin/env python3
"""Portable, read-only static and finite check. Never invokes Lean or repository code."""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
REL = Path("Computability/DiophantineConsistency/Lean/DiophantineConsistency")
NAME = "CurrentWordPadding2011.lean"
OLD_SHA = "dcf9b865df831b0c7f4de2aa0e9060c88fd62d6fae2dd0497ea0aa2f36c6b6d7"
NEW_SHA = "32b3612c45b0664b4fee21b3b1c4ae2675ba1106fab119c77a14409ccbf2c9dd"
OLD = """  apply (PaddingStaircase.bit3_mask_iff x).mpr
  have hb : (x%2048).testBit 3 = false := Nat.testBit_lt_two_pow (by omega)
  have he := Nat.testBit_mod_two_pow x 11 3
  change (x%2048).testBit 3 = _ at he
  simp only [show (3 < 11) = True from propext (by decide),decide_true,Bool.true_and] at he
  rwa [he] at hb"""
NEW = """  simpa only [PaddingStaircase.bit3_mask_iff, Nat.testBit_mod_two_pow,
    show (3 < 11) = True from propext (by decide), decide_true, Bool.true_and] using
    (Nat.testBit_lt_two_pow (show x%2^11 < 2^3 by omega))"""
SIGNATURE = "theorem bit3_clear_of_residue {x : ℕ} (hx : x%2048 ≤ 5) : x &&& 8 = 0 := by"


def require(condition: bool, label: str) -> None:
    if not condition:
        raise SystemExit("FAILED: " + label)


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def without_comments(text: str) -> str:
    # The inspected target has no nested block comments or comment-looking strings.
    return re.sub(r"--[^\n]*", "", re.sub(r"/\-.*?\-/", "", text, flags=re.S))


def metrics(text: str) -> dict[str, int]:
    code = without_comments(text)
    return {
        "physical_lines": len(text.splitlines()),
        "code_lines": sum(bool(line.strip()) for line in code.splitlines()),
        "lexical_tokens": len(re.findall(r"[\w\u0080-\uffff]+|[^\w\s]", code)),
    }


def declarations(text: str) -> list[str]:
    return re.findall(r"^(?:private )?(?:theorem|def|abbrev|structure|lemma)\s+(\S+)", text, re.M)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-tree", type=Path)
    parser.add_argument("--candidate-dir", type=Path, default=HERE / "candidates")
    args = parser.parse_args()
    tree = args.baseline_tree
    if tree is None:
        tree = HERE.parent / "baseline"
        if not tree.exists():
            tree = HERE.parent / "upstream"
    baseline = (tree / REL / NAME).read_text(encoding="utf-8")
    candidate = (args.candidate_dir / NAME).read_text(encoding="utf-8")
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    require(manifest["pin"] == "9f35798db4a63c25e435fca14d75931144657d7e", "pin metadata")
    require(sha(baseline) == OLD_SHA, "pinned target SHA-256")
    require(sha(candidate) == NEW_SHA, "candidate SHA-256")
    require(baseline.count(OLD) == 1, "unique old proof body")
    require(candidate == baseline.replace(OLD, NEW), "exact proof-only edit and unchanged surroundings")
    require(SIGNATURE in baseline and SIGNATURE in candidate, "exact Nat domain, residue guard and conclusion")
    require(declarations(baseline) == declarations(candidate), "all declaration names unchanged; no helpers")
    require(re.findall(r"^import .*", baseline, re.M) ==
            re.findall(r"^import .*", candidate, re.M), "imports unchanged")
    require(re.findall(r"^.*(?:variable|omit|section|namespace).*$", baseline, re.M) ==
            re.findall(r"^.*(?:variable|omit|section|namespace).*$", candidate, re.M), "domain and namespace scopes unchanged")
    for relative, expected in manifest["dependency_bindings"].items():
        require(sha((tree / relative).read_text(encoding="utf-8")) == expected,
                "dependency/source binding: " + relative)
    entries = manifest["candidates"]
    require(len(entries) == 1, "only one retained candidate")
    entry = entries[0]
    require(entry["old_body"] == OLD and entry["new_body"] == NEW, "manifest exact proof texts")
    require(entry["baseline_sha256"] == OLD_SHA and entry["candidate_sha256"] == NEW_SHA,
            "manifest target hashes")
    for key, text in [("old_body_metrics", OLD), ("new_body_metrics", NEW),
                      ("old_module_metrics", baseline), ("new_module_metrics", candidate)]:
        require(entry[key] == metrics(text), key)
    delta = {key: metrics(candidate)[key] - metrics(baseline)[key] for key in metrics(baseline)}
    require(delta == entry["body_delta"] == entry["module_delta"] == manifest["totals"],
            "helper-inclusive metrics and totals")
    require(entry["new_helpers"] == 0 and entry["new_imports"] == 0 and
            entry["public_contract_changed"] is False, "zero helper/import/contract overhead")
    patch = "".join(difflib.unified_diff(baseline.splitlines(True), candidate.splitlines(True),
                     fromfile="a/" + str(REL / NAME), tofile="b/" + str(REL / NAME)))
    require((HERE / "patches" / "bit3_clear_of_residue.patch").read_text(encoding="utf-8") == patch,
            "exact unified patch")
    require(not (HERE / "candidates" / "CurrentWordScalarWitness2011.lean").exists(),
            "excluded q_prefix candidate absent")

    multipliers = [0, 1, 2, 3, 17, 255, 2**32, 2**64 + 7, 2**127 - 1, 2**256 + 19]
    tested = satisfying = 0
    for multiple in multipliers:
        for residue in range(2048):
            x = 2048 * multiple + residue
            require(x % 2048 == residue, "finite representative remainder")
            require(((x % 2**11) >> 3) & 1 == ((x >> 3) & 1), "bit three survives modulo 2048")
            require((x & 8 == 0) == (((x >> 3) & 1) == 0), "mask/bit equivalence")
            if x % 2048 <= 5:
                require(x % 2**11 < 2**3, "omega arithmetic obligation")
                require(x & 8 == 0, "exact public conclusion")
                satisfying += 1
            tested += 1
    require(8 % 2048 <= 8 and (8 & 8) != 0, "counterexample if weakened residue bound admits 8")
    require(8 % 4 <= 5 and (8 & 8) != 0, "counterexample to dropping modulus size requirement")
    require(2048 > 5 and 2048 % 2048 <= 5 and (2048 & 8) == 0,
            "domain includes unbounded full digits, not only x <= 5")
    print(json.dumps({
        "status": "passed static and finite checks; Lean not run",
        "target": NAME + ".bit3_clear_of_residue",
        "pin": manifest["pin"],
        "static": {"exact_proof_only_patch": True, "unchanged_declarations": len(declarations(baseline)),
                   "dependency_bindings": len(manifest["dependency_bindings"]),
                   "helpers_added": 0, "imports_added": 0, "module_delta": delta},
        "finite": {"complete_remainder_classes": 2048, "high_multipliers": len(multipliers),
                   "bit_mask_and_modulo_cases": tested, "in_domain_implication_cases": satisfying,
                   "largest_multiple_bit_length": max(multipliers).bit_length(),
                   "guard_counterexamples": {"allow_residue_8": 8, "replace_mod2048_with_mod4": 8},
                   "unbounded_digit_witness": 2048},
        "limitations": ["Finite tests do not establish universal quantifiers.",
                        "No Lean elaboration, kernel validation, axiom check or performance timing was run.",
                        "The bit bound 5 is preserved; it is sufficient, not claimed sharp."]
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
