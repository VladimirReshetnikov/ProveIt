#!/usr/bin/env python3
"""Compile a finite quadratic integer system to one height-one quartic.

Standard-library only. The proof is in PROOF.md. This generator is intentionally
independent of upstream arithmetic and proof-checker code.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")


def normalize(source):
    original_n = len(source["variables"])
    variables = [{"kind": "original", "index": i} for i in range(original_n)]
    coefficients = set()

    def need(c):
        if c > 1 and c not in coefficients:
            coefficients.add(c)
            need(c // 2)

    for row in source["residuals"]:
        for c, mon in row["terms"]:
            if not isinstance(c, int) or c == 0 or len(mon) > 2:
                raise ValueError("Expected nonzero integer coefficients and quadratic rows")
            if any(not isinstance(i, int) or not 0 <= i < original_n for i in mon):
                raise ValueError("Source variable index out of range")
            need(abs(c))

    constant_ids = {}
    rows = []
    for c in sorted(coefficients):
        idx = len(variables)
        constant_ids[c] = idx
        variables.append({"kind": "constant", "value": c})
        half = [] if c // 2 == 1 else [constant_ids[c // 2]]
        terms = [[1, [idx]], [-1, half], [-1, half]]
        if c % 2:
            terms.append([-1, []])
        rows.append({"kind": "constant", "value": c, "terms": terms})

    scale_keys = sorted({(abs(c), mon[0]) for row in source["residuals"]
                         for c, mon in row["terms"] if abs(c) > 1 and len(mon) == 2})
    scale_ids = {}
    for c, v in scale_keys:
        idx = len(variables)
        scale_ids[c, v] = idx
        variables.append({"kind": "scale", "coefficient": c, "variable": v})
        rows.append({"kind": "scale", "coefficient": c, "variable": v,
                     "terms": [[1, [idx]], [-1, [constant_ids[c], v]]]})

    for r, row in enumerate(source["residuals"]):
        terms = []
        for c, mon in row["terms"]:
            a, sign = abs(c), 1 if c > 0 else -1
            if a == 1:
                out_mon = mon
            elif len(mon) == 0:
                out_mon = [constant_ids[a]]
            elif len(mon) == 1:
                out_mon = [constant_ids[a], mon[0]]
            else:
                out_mon = [scale_ids[a, mon[0]], mon[1]]
            terms.append([sign, out_mon])
        rows.append({"kind": "source", "source_row": r, "terms": terms})
    return {"variables": variables, "rows": rows, "original_variables": original_n,
            "constant_count": len(constant_ids), "scale_count": len(scale_ids)}


def compile_system(source):
    norm = normalize(source)
    variables, blocks, groups, units = [], [], defaultdict(list), []
    polynomial = {}

    def fresh(kind, **data):
        idx = len(variables)
        variables.append({"kind": kind, **data})
        return idx

    def term(coef, mon):
        key = tuple(sorted(mon))
        if coef not in (-1, 1) or key in polynomial:
            raise ValueError("Coefficient collision; height-one construction invariant failed")
        polynomial[key] = coef

    for r, row in enumerate(norm["rows"]):
        signs, products, witnesses = [], [], []
        for j, (sign, mon) in enumerate(row["terms"]):
            aliases = []
            for k in range(2):
                if k < len(mon):
                    old = mon[k]
                    a = fresh("alias", normalized_variable=old, row=r, occurrence=j, slot=k)
                    groups[old].append(a)
                else:
                    a = fresh("unit", row=r, occurrence=j, slot=k)
                    units.append(a)
                aliases.append(a)
            w = fresh("product", row=r, occurrence=j)
            signs.append(sign)
            products.append(aliases)
            witnesses.append(w)
            term(1, aliases + aliases)
            term(1, [w, w])
            term(-1, aliases + [w])
        for i in range(len(signs)):
            for j in range(i + 1, len(signs)):
                term(signs[i] * signs[j], products[i] + products[j])
                term(signs[i] * signs[j], [witnesses[i], witnesses[j]])
        blocks.append({"normalized_row": r, "signs": signs,
                       "products": products, "witnesses": witnesses})

    cycles = []
    for old, aliases in sorted(groups.items()):
        if len(aliases) == 1:
            cycles.append({"normalized_variable": old, "aliases": aliases, "singleton": True})
            continue
        if len(aliases) == 2:
            aliases.append(fresh("equality_dummy", normalized_variable=old))
        for a in aliases:
            term(1, [a, a])
        for i, a in enumerate(aliases):
            term(-1, [a, aliases[(i + 1) % len(aliases)]])
        cycles.append({"normalized_variable": old, "aliases": aliases, "singleton": False})
    while len(units) < 2:
        units.append(fresh("unit_dummy"))
    term(1, [])
    for a in units:
        term(1, [a, a])
    term(-1, [units[0]])
    term(-1, [units[-1]])
    for a, b in zip(units, units[1:]):
        term(-1, [a, b])

    terms = [[polynomial[k], list(k)] for k in sorted(polynomial, key=lambda m: (len(m), m))]
    metrics = {"domain": "unrestricted integers", "variables": len(variables),
               "degree": max(map(len, polynomial)), "coefficient_height": 1,
               "monomials": len(terms), "original_variables": len(source["variables"]),
               "original_rows": len(source["residuals"]), "normalized_variables": len(norm["variables"]),
               "normalized_rows": len(norm["rows"]), "unit_term_occurrences": sum(len(b["signs"]) for b in blocks),
               "equality_dummies": sum(v["kind"] == "equality_dummy" for v in variables),
               "unit_aliases": len(units), "constant_count": norm["constant_count"],
               "scale_count": norm["scale_count"],
               "positive_coefficients": sum(c == 1 for c, m in terms),
               "negative_coefficients": sum(c == -1 for c, m in terms)}
    artifact = {"schema": "height-one-quartic-v1", "domain": "unrestricted integers",
                "variables": variables, "terms": terms, "metrics": metrics}
    certificate = {"schema": "height-one-certificate-v1", "normalization": norm,
                   "blocks": blocks, "equality_cycles": cycles, "unit_path": units}
    return artifact, certificate


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=here / "source/equation.json")
    parser.add_argument("--out", type=Path, default=here / "output")
    args = parser.parse_args()
    raw = args.source.read_bytes()
    source = json.loads(raw)
    artifact, certificate = compile_system(source)
    certificate["source_sha256"] = hashlib.sha256(raw).hexdigest()
    write_json(args.out / "polynomial.json", artifact)
    write_json(args.out / "certificate.json", certificate)
    write_json(args.out / "METRICS.json", artifact["metrics"])
    print(json.dumps(artifact["metrics"], sort_keys=True))


if __name__ == "__main__":
    main()
