#!/usr/bin/env python3
"""Independent exact finite verifier for the prime-supported P209 quartic.

Uses Python's standard library and no producer/inherited polynomial code.
The checks remain active under -O. They do not prove unbounded semantics.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from math import isqrt
from pathlib import Path
import zipfile

PARENT_SHA256 = "20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a"
PRIME = 524309
LABEL_DEGREE = 1 << 19
PARENT_ARCHIVE = "ConZFC_Pell_Growth_210_2026-10-25.zip"
PARENT_MEMBER = "ConZFC_Pell_Growth_210_2026-10-25/equations/principal210/equation.json"

class VerificationError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def parse_terms(raw, arity, degree_bound):
    require(isinstance(raw, list), "term list is not a list")
    answer = {}
    for item in raw:
        require(isinstance(item, list) and len(item) == 2, "malformed term")
        coefficient, variables = item
        require(type(coefficient) is int and coefficient != 0, "invalid coefficient")
        require(isinstance(variables, list), "invalid monomial")
        require(len(variables) <= degree_bound, "degree exceeds bound")
        require(all(type(i) is int and 0 <= i < arity for i in variables), "invalid index")
        require(variables == sorted(variables), "unsorted monomial")
        key = tuple(variables)
        require(key not in answer, "duplicate monomial")
        answer[key] = coefficient
    return answer

def combine(a, b, multiplier=1):
    answer = dict(a)
    for monomial, coefficient in b.items():
        value = answer.get(monomial, 0) + multiplier * coefficient
        if value:
            answer[monomial] = value
        else:
            answer.pop(monomial, None)
    return answer

def square(a):
    answer = {}
    entries = list(a.items())
    for i, (left, lc) in enumerate(entries):
        for j in range(i, len(entries)):
            right, rc = entries[j]
            monomial = tuple(sorted(left + right))
            factor = 1 if i == j else 2
            answer[monomial] = answer.get(monomial, 0) + factor * lc * rc
    return {m: c for m, c in answer.items() if c}

def sum_of_squares(rows):
    answer = {}
    for row in rows:
        answer = combine(answer, square(row))
    return answer

def read_rows(equation, arity, count):
    require(equation.get("domain") == "unrestricted integers", "incorrect domain")
    require(isinstance(equation.get("variables"), list), "missing coordinates")
    require(len(equation["variables"]) == arity, "wrong coordinate count")
    raw = equation.get("residuals")
    require(isinstance(raw, list) and len(raw) == count, "wrong row count")
    return [parse_terms(row.get("terms"), arity, 2) for row in raw]

def reconstruct(parent):
    rows = read_rows(parent, 210, 150)
    bindings = {0: "t0", 2: "growth.F", 3: "choose0.output", 4: "beta.y_plus_one",
                178: "cofinal.horizon_root", 206: "beta.odd_multiplier_half",
                207: "growth_pell.X", 208: "growth_pell.tF", 209: "growth_pell.odd_half"}
    for i, name in bindings.items():
        require(parent["variables"][i].get("name") == name, f"parent coordinate {i}")
    # Undo the old beta-row addition before replacing its relation.
    rows[3] = combine(rows[3], rows[146], -1)
    rows[125] = {(): -32, (0,): 1, (178,): -128, (178, 178): -128}
    rows[146] = {(): -1, (4,): 1, (2, 3): -1}
    rows[147] = {(208,): 1, (0, 2): -PRIME}
    rows[148] = {(): -1, (207, 207): 1, (208, 208): -1, (2, 208): -2}
    rows[149] = {(2,): 1, (0,): 1, (0, 209): -PRIME}
    require(all(206 not in m for row in rows for m in row), "deleted variable remains")
    renaming = {i: i if i < 206 else i - 1 for i in range(210) if i != 206}
    require(set(renaming.values()) == set(range(209)), "coordinate map is not bijective")
    return [{tuple(renaming[i] for i in m): c for m, c in row.items()} for row in rows]

def get_metrics(rows, polynomial):
    require(polynomial, "zero polynomial")
    used_rows = {i for row in rows for m in row for i in m}
    used_polynomial = {i for m in polynomial for i in m}
    require(used_rows == set(range(209)), "unused residual coordinate")
    require(used_polynomial == set(range(209)), "unused polynomial coordinate")
    require(max(map(len, polynomial)) == 4, "not exact degree four")
    return {"variables": 209, "squared_residuals": len(rows),
            "degree": max(map(len, polynomial)), "monomials": len(polynomial),
            "coefficient_height": max(abs(c) for c in polynomial.values()),
            "maximum_residual_coefficient": max(abs(c) for row in rows for c in row.values()),
            "residual_monomials": sum(map(len, rows))}

def compare_rows(actual, expected):
    require(len(actual) == len(expected), "row count mismatch")
    for i, (a, b) in enumerate(zip(actual, expected)):
        require(a == b, f"literal coefficient mismatch in row {i}")

def mutation_controls(final, expected, expansion):
    tested = []
    for index in [0, 3, 125, 146, 147, 148, 149]:
        bad = copy.deepcopy(final)
        old = bad["residuals"][index]["terms"][0][0]
        bad["residuals"][index]["terms"][0][0] = old + (1 if old > 0 else -1)
        try:
            compare_rows(read_rows(bad, 209, 150), expected)
        except VerificationError:
            tested.append(f"row_{index}_coefficient")
        else:
            raise VerificationError(f"row {index} mutation escaped detection")
    bad = dict(expansion)
    monomial = next(iter(bad))
    bad[monomial] += 1
    try:
        require(bad == expansion, "expanded coefficient mismatch")
    except VerificationError:
        tested.append("expanded_coefficient")
    else:
        raise VerificationError("expanded coefficient mutation escaped detection")
    return tested

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--parent", type=Path)
    parser.add_argument("--equation-dir", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--metrics-only", action="store_true")
    args = parser.parse_args()
    if args.parent:
        parent_bytes = args.parent.read_bytes()
    elif (args.root / "inherited/parent210_equation.json").exists():
        parent_bytes = (args.root / "inherited/parent210_equation.json").read_bytes()
    else:
        with zipfile.ZipFile(args.root / "inherited" / PARENT_ARCHIVE) as archive:
            parent_bytes = archive.read(PARENT_MEMBER)
    require(hashlib.sha256(parent_bytes).hexdigest() == PARENT_SHA256, "parent byte identity")
    parent = json.loads(parent_bytes)
    require(PRIME > LABEL_DEGREE and PRIME > 33 and PRIME % 2 == 1, "constant prerequisites")
    for divisor in range(2, isqrt(PRIME) + 1):
        require(PRIME % divisor != 0, "declared prime is composite")
    expected = reconstruct(parent)
    expansion = sum_of_squares(expected)
    metrics = get_metrics(expected, expansion)
    receipt = {"status": "reconstructed" if args.metrics_only else "PASS",
               "parent_sha256": PARENT_SHA256, "prime": PRIME,
               "prime_trial_divisor_maximum": isqrt(PRIME), "metrics": metrics,
               "scope": "Exact finite coefficients; not an unbounded semantic proof"}
    if not args.metrics_only:
        directory = args.equation_dir or args.root / "equations"
        final_bytes = (directory / "equation.json").read_bytes()
        final = json.loads(final_bytes)
        compare_rows(read_rows(final, 209, 150), expected)
        raw_expansion = json.loads((directory / "expanded_polynomial.json").read_text())
        require(raw_expansion.get("variables") == 209, "expanded coordinate count")
        actual_expansion = parse_terms(raw_expansion.get("terms"), 209, 4)
        require(actual_expansion == expansion, "collected polynomial mismatch")
        actual_metrics = json.loads((directory / "metrics.json").read_text())
        for name, value in metrics.items():
            require(actual_metrics.get(name) == value, f"metric mismatch: {name}")
        receipt["equation_sha256"] = hashlib.sha256(final_bytes).hexdigest()
        receipt["mutation_controls_rejected"] = mutation_controls(final, expected, expansion)
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end="")

if __name__ == "__main__":
    main()
