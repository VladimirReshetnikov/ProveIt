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


ROW_PRIORITY=()
SOURCE_SHA256='0bace72d00da17b5202a9caac2394fbe5543891a3e289893c7d6e9205f04b96c'

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
    p.add_argument("--priority", type=Path, required=True)
    args = p.parse_args()
    global ROW_PRIORITY
    ROW_PRIORITY = tuple(json.loads(args.priority.read_text()))
    source = json.loads(args.input.read_text())
    require(sorted(ROW_PRIORITY)==list(range(len(source["residuals"]))),"priority must be a permutation")
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
