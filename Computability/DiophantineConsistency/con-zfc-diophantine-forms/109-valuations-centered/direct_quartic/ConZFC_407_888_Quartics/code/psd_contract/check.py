#!/usr/bin/env python3
"""Independent exact replay of certified nonnegative contractions.

Imports no producer module.  It expands every rational square certificate,
checks its integer identity, and replays substitution from occurrence lists.
"""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def collect(terms):
    out = {}
    for coefficient, monomial in terms:
        key = tuple(sorted(monomial))
        out[key] = out.get(key, 0)+coefficient
    return [[c, list(m)] for m, c in sorted(out.items()) if c]


def q(value):
    require(isinstance(value, list) and len(value) == 2 and all(type(x) is int for x in value), "bad rational")
    require(value[1] > 0, "positive denominator required")
    return Fraction(value[0], value[1])


def verify_nonnegative(restoration, proof):
    terms = []
    for c, m in proof["nonnegative_remainder"]:
        require(type(c) is int and c > 0 and len(m) <= 2, "invalid nonnegative remainder")
        terms.append((Fraction(c), m))
    for square in proof["squares"]:
        weight = q(square["weight"])
        require(weight > 0, "square weight must be positive")
        form = [(q(c), m) for c, m in square["affine_form"]]
        require(all(len(m) <= 1 for c, m in form), "nonaffine square form")
        for a, ma in form:
            for b, mb in form:
                terms.append((weight*a*b, ma+mb))
    actual = collect(terms)
    require(all(c.denominator == 1 for c, m in actual), "certificate does not have integer coefficients")
    require([[int(c), m] for c, m in actual] == restoration, "sum-of-squares identity failed")


def verify(source, target, cert):
    require(cert["source_equation_sha256"] == sha256(canonical(source)).hexdigest(), "source hash")
    require(cert["target_equation_sha256"] == sha256(canonical(target)).hexdigest(), "target hash")
    require(source["domain"] == target["domain"] == "nonnegative integers", "wrong domain")
    rows = {i: collect(row["terms"]) for i, row in enumerate(source["residuals"])}
    live = set(range(len(source["variables"])))
    signed = 0
    for step in cert["steps"]:
        rid, var = step["source_row_id"], step["variable_original_index"]
        require(rid in rows and var in live, "invalid pivot")
        require(rows[rid] == step["row_before"], "pivot row mismatch")
        sign, restoration = step["pivot_sign"], step["restoration"]
        require(sign in (-1, 1), "pivot is not monic")
        require(len(restoration) <= cert["support_cap"], "support cap")
        require(all(type(c) is int and len(m) <= 2 and var not in m and set(m) <= live for c, m in restoration), "bad restoration")
        verify_nonnegative(restoration, step["nonnegative_certificate"])
        signed += any(c < 0 for c, m in restoration)
        expected = collect([[sign, [var]]]+[[-sign*c, m] for c, m in restoration])
        require(rows[rid] == expected, "pivot identity")
        del rows[rid]
        for i, row in rows.items():
            terms = []
            for coefficient, monomial in row:
                products = [[coefficient, []]]
                for atom in monomial:
                    factor = restoration if atom == var else [[1, [atom]]]
                    products = [[a*b, ma+mb] for a, ma in products for b, mb in factor]
                terms.extend(products)
            rows[i] = collect(terms)
            require(all(len(m) <= 2 for c, m in rows[i]), "degree bound lost")
        live.remove(var)
    retained = cert["retained_original_indices_in_target_order"]
    unused = cert["unused_original_indices_restored_to_zero"]
    require(set(retained).isdisjoint(unused) and set(retained)|set(unused) == live, "live partition")
    require(set(retained) == {v for row in rows.values() for c, m in row for v in m}, "retained variables")
    ids = [i for i in sorted(rows) if rows[i]]
    require(ids == cert["surviving_source_row_ids_in_target_order"], "surviving rows")
    require([i for i in sorted(rows) if not rows[i]] == cert["zero_source_row_ids"], "zero rows")
    rename = {v: i for i, v in enumerate(retained)}
    require(len(target["residuals"]) == len(ids), "target row count")
    for row, rid in zip(target["residuals"], ids):
        expected = collect([[c, [rename[v] for v in m]] for c, m in rows[rid]])
        require(row["terms"] == expected and row["label"] == source["residuals"][rid]["label"], "target residual")
    require(target["variables"] == [source["variables"][i] for i in retained], "target coordinates")
    # Independent expansion of the final sum of squares.
    allterms = []
    for row in target["residuals"]:
        for a, ma in row["terms"]:
            for b, mb in row["terms"]:
                allterms.append((a*b, ma+mb))
    expanded = collect(allterms)
    return {"verified": True, "variables": len(retained), "rows": len(ids),
            "eliminations": len(cert["steps"]), "negative_coefficient_restorations": signed,
            "exact_degree": max((len(m) for c, m in expanded), default=0),
            "expanded_monomials": len(expanded),
            "coefficient_height": max((abs(c) for c, m in expanded), default=0),
            "method": "independent rational square expansion and occurrence-list substitution"}, expanded


def main():
    p = argparse.ArgumentParser()
    p.add_argument("source", type=Path)
    p.add_argument("target_dir", type=Path)
    args = p.parse_args()
    target = json.loads((args.target_dir/"equation.json").read_text())
    cert = json.loads((args.target_dir/"elimination_certificate.json").read_text())
    result, expanded = verify(json.loads(args.source.read_text()), target, cert)
    recorded = json.loads((args.target_dir/"expanded_polynomial.json").read_text())
    require(recorded["terms"] == expanded, "recorded expansion differs")
    (args.target_dir/"VERIFICATION.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
