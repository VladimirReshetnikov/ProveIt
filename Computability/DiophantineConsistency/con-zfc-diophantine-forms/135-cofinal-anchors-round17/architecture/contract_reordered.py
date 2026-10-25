#!/usr/bin/env python3
"""Exact quadratic contraction with explicit rational sum-of-squares witnesses.

Each eliminated coordinate is restored by an integer polynomial P.  A retained
certificate writes P as a positive rational combination of squares of affine
rational forms plus an integer polynomial with nonnegative coefficients.
Hence P is nonnegative on N^k, even if its expanded coefficients have signs.
All identities and subsequent substitutions are independently replayable.
"""
from copy import deepcopy
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


def loadpoly(terms):
    out = {}
    for coefficient, monomial in terms:
        require(type(coefficient) is int, "coefficient must be an integer")
        m = tuple(sorted(monomial))
        out[m] = out.get(m, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def dump(poly):
    return [[c, list(m)] for m, c in sorted(poly.items()) if c]


def multiply(left, right):
    out = {}
    for m, a in left.items():
        for n, b in right.items():
            k = tuple(sorted(m+n))
            out[k] = out.get(k, 0) + a*b
    return {m: c for m, c in out.items() if c}


def subst(poly, var, definition):
    out = {}
    for monomial, coefficient in poly.items():
        term = {(): coefficient}
        for index in monomial:
            term = multiply(term, definition if index == var else {(index,): 1})
        for m, c in term.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def rational(q):
    return [q.numerator, q.denominator]


def gram_squares(poly):
    """Return exact LDL square terms if the homogeneous Gram matrix is PSD."""
    nodes = sorted({-1 if not m else m[0] for m in poly} |
                   {v for m in poly for v in m} |
                   ({-1} if any(len(m) < 2 for m in poly) else set()))
    pos = {v: i for i, v in enumerate(nodes)}
    a = [[Fraction(0) for _ in nodes] for _ in nodes]
    for m, c in poly.items():
        i, j = ([pos[-1], pos[-1]] if not m else
                [pos[-1], pos[m[0]]] if len(m) == 1 else
                [pos[m[0]], pos[m[1]]])
        if i == j:
            a[i][j] += c
        else:
            a[i][j] += Fraction(c, 2)
            a[j][i] += Fraction(c, 2)
    live = list(range(len(nodes)))
    squares = []
    while live:
        if any(a[i][i] < 0 for i in live):
            return None
        pivot = next((i for i in live if a[i][i] > 0), None)
        if pivot is None:
            return squares if all(a[i][j] == 0 for i in live for j in live) else None
        d = a[pivot][pivot]
        form = []
        for j in live:
            if a[pivot][j]:
                q = a[pivot][j] / d
                form.append([rational(q), [] if nodes[j] == -1 else [nodes[j]]])
        squares.append({"weight": rational(d), "affine_form": form})
        rest = [i for i in live if i != pivot]
        for i in rest:
            for j in rest:
                a[i][j] -= a[i][pivot]*a[pivot][j]/d
        live = rest
    return squares


def nonnegative_certificate(poly):
    if all(c >= 0 for c in poly.values()):
        return {"squares": [], "nonnegative_remainder": dump(poly), "method": "coefficientwise"}
    if any(len(m) > 2 for m in poly):
        return None
    # Three sufficient recognizers, each accepted only after an exact PSD test.
    # The last retains positive edges internal to a negative-edge component,
    # allowing squares such as (x+y-z)^2 while dropping unrelated xy terms.
    parent = {}
    def find(v):
        parent.setdefault(v, v)
        while parent[v] != v:
            v = parent[v]
        return v
    def union(x, y):
        x, y = find(x), find(y)
        parent[x] = y
    for m, c in poly.items():
        if c < 0 and len(m) in (1, 2):
            x, y = (-1, m[0]) if len(m) == 1 else m
            union(x, y)
    for mode in ("full_psd", "negative_edges", "negative_components"):
        remainder = {}
        for m, c in poly.items():
            if mode == "full_psd" or c <= 0 or not m or (len(m) == 2 and m[0] == m[1]):
                continue
            x, y = (-1, m[0]) if len(m) == 1 else m
            if mode == "negative_edges" or find(x) != find(y):
                remainder[m] = c
        core = {m: c for m, c in poly.items() if m not in remainder}
        squares = gram_squares(core)
        if squares is not None:
            return {"squares": squares, "nonnegative_remainder": dump(remainder), "method": mode}
    return None


def metrics_and_polynomial(equation):
    total = {}
    maxrow = 0
    for record in equation["residuals"]:
        row = loadpoly(record["terms"])
        maxrow = max(maxrow, *(abs(c) for c in row.values()))
        for m, c in multiply(row, row).items():
            total[m] = total.get(m, 0) + c
    total = {m: c for m, c in total.items() if c}
    metrics = {"variables": len(equation["variables"]),
               "quadratic_rows": len(equation["residuals"]),
               "exact_degree": max(map(len, total), default=0),
               "expanded_monomials": len(total),
               "max_abs_expanded_coefficient": max(map(abs, total.values()), default=0),
               "max_abs_row_coefficient": maxrow}
    polynomial = {"schema": "sparse_integer_polynomial_v1", "domain": equation["domain"],
                  "variables": metrics["variables"], "terms": dump(total)}
    return metrics, polynomial


ROW_PRIORITY=(57, 67, 135, 277, 261, 182, 189, 247, 263, 184, 214, 161, 206, 19, 282, 90, 69, 35, 48, 87, 173, 252, 143, 227, 71, 210, 258, 257, 244, 211, 4, 248, 33, 170, 41, 152, 49, 47, 86, 43, 205, 53, 249, 34, 91, 101, 131, 74, 76, 234, 93, 88, 236, 83, 155, 256, 251, 191, 260, 162, 140, 0, 165, 254, 183, 24, 120, 197, 150, 188, 220, 245, 187, 259, 232, 222, 142, 6, 97, 281, 200, 280, 40, 13, 80, 262, 70, 136, 17, 212, 56, 241, 124, 141, 82, 207, 30, 115, 198, 169, 96, 147, 146, 157, 73, 38, 219, 194, 54, 84, 139, 52, 110, 250, 105, 63, 85, 46, 180, 243, 28, 64, 221, 51, 264, 223, 216, 32, 231, 192, 235, 111, 208, 137, 238, 27, 106, 159, 55, 255, 98, 128, 283, 109, 50, 7, 15, 153, 253, 225, 119, 118, 199, 9, 104, 99, 68, 37, 26, 172, 177, 134, 193, 176, 149, 45, 61, 65, 163, 229, 175, 12, 29, 195, 160, 100, 276, 62, 275, 196, 23, 25, 190, 58, 18, 204, 174, 268, 130, 122, 226, 269, 102, 166, 168, 239, 138, 8, 94, 103, 59, 181, 36, 271, 167, 127, 20, 156, 224, 31, 203, 178, 273, 218, 230, 215, 272, 3, 217, 186, 123, 179, 42, 16, 278, 117, 81, 77, 79, 39, 125, 60, 95, 133, 1, 202, 279, 21, 267, 265, 148, 75, 144, 242, 44, 164, 274, 108, 126, 89, 22, 201, 107, 66, 92, 266, 114, 270, 233, 237, 14, 78, 10, 129, 112, 11, 158, 72, 171, 154, 151, 5, 113, 121, 132, 209, 2, 228, 116, 213, 145, 246, 240, 185)
SOURCE_SHA256='813dd62f6a62a294121a9c9c023af8303bb2e7980cb1615e39e206b64d20008c'

def contract(source, support_cap=64, protected_variables=()):
    require(source["domain"] == "nonnegative integers", "source domain")
    rows = {i: loadpoly(r["terms"]) for i, r in enumerate(source["residuals"])}
    require(all(len(m) <= 2 for r in rows.values() for m in r), "quadratic source required")
    live = set(range(len(source["variables"])))
    protected = set(protected_variables)
    steps, cache = [], {}
    require(sha256(canonical(source)).hexdigest()==SOURCE_SHA256,'wrong source for fixed elimination priority')
    def order_key(item):
        return ROW_PRIORITY[item[0]]
    while True:
        nonlinear = {v for r in rows.values() for m in r if len(m) > 1 for v in m}
        selected = None
        for rowid, row in sorted(rows.items(), key=lambda item: order_key(item)):
            for m, sign in sorted(row.items()):
                if len(m) != 1 or abs(sign) != 1 or m[0] not in live or m[0] in protected:
                    continue
                var = m[0]
                definition = {n: -sign*c for n, c in row.items() if n != m}
                if len(definition) > support_cap or any(var in n for n in definition):
                    continue
                if var in nonlinear and any(len(n) == 2 for n in definition):
                    continue
                key = tuple(sorted(definition.items()))
                if key not in cache:
                    cache[key] = nonnegative_certificate(definition)
                witness = cache[key]
                if witness is not None:
                    selected = rowid, var, sign, definition, witness
                    break
            if selected is not None:
                break
        if selected is None:
            break
        rowid, var, sign, definition, witness = selected
        steps.append({"source_row_id": rowid, "variable_original_index": var,
                      "variable_name": source["variables"][var]["name"], "pivot_sign": sign,
                      "row_before": dump(rows[rowid]), "restoration": dump(definition),
                      "nonnegative_certificate": witness})
        del rows[rowid]
        rows = {i: subst(r, var, definition) for i, r in rows.items()}
        require(all(len(m) <= 2 for r in rows.values() for m in r), "contraction lost degree")
        live.remove(var)
    used = {v for r in rows.values() for m in r for v in m}
    retained = sorted(used)
    renaming = {v: i for i, v in enumerate(retained)}
    ids = [i for i in sorted(rows) if rows[i]]
    target = deepcopy(source)
    target["variables"] = [deepcopy(source["variables"][i]) for i in retained]
    target["residuals"] = [{"label": source["residuals"][i]["label"],
                             "terms": dump({tuple(renaming[v] for v in m): c for m, c in rows[i].items()})}
                            for i in ids]
    target["variant"] = source.get("variant", "source") + ".certified_nonnegative_cap" + str(support_cap)
    met, poly = metrics_and_polynomial(target)
    target["metrics"].update(met)
    kinds = {}
    for variable in target["variables"]:
        kind = variable.get("kind", "unspecified")
        kinds[kind] = kinds.get(kind, 0)+1
    target["metrics"]["variable_kinds"] = dict(sorted(kinds.items()))
    target["metrics"]["nonnegative_certified_eliminations"] = len(steps)
    cert = {"schema": "rational_sos_monic_elimination_v1", "support_cap": support_cap,
            "source_equation_sha256": sha256(canonical(source)).hexdigest(),
            "target_equation_sha256": sha256(canonical(target)).hexdigest(), "steps": steps,
            "retained_original_indices_in_target_order": retained,
            "unused_original_indices_restored_to_zero": sorted(live-used),
            "surviving_source_row_ids_in_target_order": ids,
            "zero_source_row_ids": [i for i in sorted(rows) if not rows[i]],
            "theorem": "Each restoration is an integer polynomial equal to a rational sum of nonnegative squares plus nonnegative monomials. Reverse restoration preserves natural domains, and exact substitution preserves every row and degree bound."}
    return target, cert, poly


def main():
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--support-cap", type=int, default=32)
    args = p.parse_args()
    source = json.loads(args.input.read_text())
    target, cert, poly = contract(source, args.support_cap)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, value in (("equation.json", target), ("elimination_certificate.json", cert),
                        ("expanded_polynomial.json", poly)):
        (args.output/name).write_text(json.dumps(value, indent=2, sort_keys=True)+"\n")
    print(json.dumps(target["metrics"], indent=2))
    print(json.dumps({"negative_coefficient_restorations": sum(any(c<0 for c,m in s["restoration"]) for s in cert["steps"]),
                      "nonnegative_certified_eliminations": len(cert["steps"])}, indent=2))


if __name__ == "__main__":
    main()
