#!/usr/bin/env python3
"""Read-only static/finite checks for optional Gamma_pos consequence reuse.

Uses only the Python standard library and files bundled beside this script.
It does not invoke Lean, git, a shell, network, or any prior packet script;
it does not write files. Passing is not Lean elaboration/kernel validation.
Run: python3 units/checks/check_units.py
"""
from pathlib import Path
from math import gcd
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
meta = json.loads((ROOT / "provenance.json").read_text())
name = "CurrentControllerUnits2011.lean"
before = (ROOT / "baseline" / name).read_text()
after = (ROOT / "candidates" / name).read_text()
patch = (ROOT / "patches/gamma_pos_from_coprime.patch").read_text()
results = {}

def check(label, condition):
    if not condition:
        raise AssertionError(label)
    results[label] = True

check("baseline_sha256", hashlib.sha256(before.encode()).hexdigest() == meta["source_sha256"])
check("candidate_sha256", hashlib.sha256(after.encode()).hexdigest() == meta["candidate_sha256"])
old = """theorem Gamma_pos (rw n : ℕ) : 0 < Gamma rw n := by
  have hq := q_gt_one n
  have hs : 0 < q n^2-1 := Nat.sub_pos_of_lt (by nlinarith)
  have hr : 0 < CurrentMasks2011.radix^977 := pow_pos (by decide) _
  exact mul_pos (mul_pos hr hs) (by omega)
"""
new = """theorem Gamma_pos (rw n : ℕ) : 0 < Gamma rw n :=
  Nat.pos_of_ne_zero fun hz => by simpa [hz] using coprime_Gamma_47 rw n
"""
check("single_proof_only_change", before.count(old) == 1 and before.replace(old, new) == after)
check("statement_identical", old.split(":=")[0] == new.split(":=")[0])
check("full_file_accounting", (len(before.splitlines()), len(after.splitlines())) == (201, 198))
check("zero_helper_cost", meta["new_helper_lines"] == 0)
check("exact_unified_diff", patch == "".join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True),
    fromfile="a/" + meta["source_relative_path"],
    tofile="b/" + meta["source_relative_path"])))
check("no_added_import", re.findall(r"^import .*", before, re.M) == re.findall(r"^import .*", after, re.M))
check("no_added_axiom_or_placeholder", not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", new))
check("unit_fact_precedes_positivity", after.index("theorem coprime_Gamma_47") < after.index("theorem Gamma_pos"))
check("coprime_does_not_depend_on_Gamma_pos", "Gamma_pos" not in after[:after.index("theorem Gamma_pos")])

# Direct finite check of the exact mathematical implication used by the patch.
# The proof is not a finite argument: gcd(0,47)=47 != 1 excludes zero for every x.
check("zero_is_not_coprime_to_47", gcd(0, 47) != 1)
check("coprime_47_implies_positive_finite", all(gcd(x,47) != 1 or x > 0 for x in range(10001)))
check("modulus_one_counterexample_preserved", gcd(0,1) == 1)
check("integer_sign_counterexample_preserved", gcd(-1,47) == 1 and not -1 > 0)

# Modular smoke checks for the unchanged upstream calibration. These read only
# fixed public constants; they are not an independent full-kernel evaluation.
aux = 120199
calibration = [(47,37,26,5,29), (2011,1283,1995,1090,674),
               (aux,37435,114787,99282,36379)]
finite_cases = 0
residues = {}
for p, b, k, quadratic, coupling in calibration:
    check(f"B_mod_{p}", pow(2,94517,p) == b)
    radix = pow(2,47,p)
    values = [pow(b,aux**n,p) for n in range(7)]
    check(f"power_dimension_{p}_n0_through6", all(q == b for q in values))
    check(f"quadratic_mod_{p}", (b*b-1) % p == quadratic)
    gamma_values = set()
    for n, q in enumerate(values):
        for rw, qw in enumerate(values):
            c = (1+q*(k+qw)) % p
            check(f"coupling_{p}_{rw}_{n}", c == coupling)
            gamma = pow(radix,977,p) * ((q*q-1) % p) * c % p
            check(f"coprime_{p}_{rw}_{n}", gcd(gamma,p) == 1)
            gamma_values.add(gamma)
            finite_cases += 1
    residues[str(p)] = sorted(gamma_values)
check("q_one_degeneracy", (1**2-1) == 0 and gcd(0,47) != 1)
print(json.dumps({"status":"passed", "checks":len(results),
                  "finite_modular_cases":finite_cases,
                  "gamma_residues_from_supplied_calibration":residues,
                  "full_file_lines_before":201,"full_file_lines_after":198,
                  "new_helper_lines":0,"net_lines_saved":3,
                  "lean_elaboration":"not_run", "kernel_validation":"not_run",
                  "independent_full_kernel_evaluation":False,
                  "upstream_mutation":False}, indent=2))
