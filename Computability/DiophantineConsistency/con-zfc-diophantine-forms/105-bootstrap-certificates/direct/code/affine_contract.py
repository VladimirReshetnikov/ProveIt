#!/usr/bin/env python3
"""Deterministic nonnegative monic-affine contraction of quadratic systems.

This module does not trust a builder's gate annotations. Every candidate is
recognized from the exported residual itself. Original variable and row indices
are retained throughout elimination; reindexing occurs exactly once at export.

For a row eps*(x-P)=0, eps in {-1,1}, where P is an affine polynomial
with nonnegative integer coefficients and does not contain x, substitution
gives a bijection of nonnegative zero sets. The inverse is polynomial and
nonnegative. The certificate records every such elementary elimination.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def unpack(terms):
    result = {}
    for coefficient, variables in terms:
        require(isinstance(coefficient, int), "noninteger coefficient")
        key = tuple(sorted(variables))
        result[key] = result.get(key, 0) + coefficient
    return {key: coefficient for key, coefficient in result.items() if coefficient}


def pack(poly):
    return [[coefficient, list(key)] for key, coefficient in sorted(poly.items()) if coefficient]


def mul(left, right):
    result = {}
    for a, ca in left.items():
        for b, cb in right.items():
            key = tuple(sorted(a + b))
            result[key] = result.get(key, 0) + ca * cb
    return {key: coefficient for key, coefficient in result.items() if coefficient}


def substitute(poly, variable, definition):
    result = {}
    for key, coefficient in poly.items():
        if variable not in key:
            result[key] = result.get(key, 0) + coefficient
            continue
        term = {(): coefficient}
        for index in key:
            term = mul(term, definition if index == variable else {(index,): 1})
        for key2, coefficient2 in term.items():
            result[key2] = result.get(key2, 0) + coefficient2
    return {key: coefficient for key, coefficient in result.items() if coefficient}


def candidates(rows, live, support_cap, terminal_quadratic=False):
    nonlinear_use = {v for row in rows.values() for key in row if len(key) > 1 for v in key}
    for row_id in sorted(rows):
        row = rows[row_id]
        if not row or (not terminal_quadratic and any(len(key) > 1 for key in row)):
            continue
        for key, sign in sorted(row.items()):
            if len(key) != 1 or abs(sign) != 1 or key[0] not in live:
                continue
            definition = {m: -c * sign for m, c in row.items() if m != key}
            if len(definition) > support_cap or any(c < 0 for c in definition.values()):
                continue
            if any(key[0] in m for m in definition):
                continue
            if any(len(m) > 1 for m in definition) and key[0] in nonlinear_use:
                continue
            yield row_id, key[0], sign, definition


def polynomial_and_metrics(residuals, variable_count):
    polynomial = {}
    maxrow = 0
    for row in residuals:
        poly = unpack(row["terms"])
        maxrow = max(maxrow, *(abs(c) for c in poly.values()))
        for key, coefficient in mul(poly, poly).items():
            polynomial[key] = polynomial.get(key, 0) + coefficient
    polynomial = {key: c for key, c in polynomial.items() if c}
    return {
        "schema": "sparse_integer_polynomial_v1",
        "domain": "nonnegative integers",
        "variables": variable_count,
        "terms": pack(polynomial),
    }, {
        "variables": variable_count,
        "quadratic_rows": len(residuals),
        "exact_degree": max((len(key) for key in polynomial), default=0),
        "expanded_monomials": len(polynomial),
        "max_abs_expanded_coefficient": max((abs(c) for c in polynomial.values()), default=0),
        "max_abs_row_coefficient": maxrow,
    }


def contract(equation, support_cap=4, protected_variables=(), terminal_quadratic=False):
    """Return (contracted_equation, full_elimination_certificate).

    Choose the earliest current row and, within it, the earliest eligible
    original variable. support_cap bounds the number of nonzero terms in each
    affine restoration, counting its constant term. All coefficients in every
    restoration are nonnegative. Protected indices are an optional interface
    convenience; they are not needed for correctness.
    """
    require(equation["domain"] == "nonnegative integers", "unexpected domain")
    require(support_cap >= 1, "positive support cap required")
    rows = {i: unpack(row["terms"]) for i, row in enumerate(equation["residuals"])}
    require(all(len(key) <= 2 for row in rows.values() for key in row), "nonquadratic source")
    live = set(range(len(equation["variables"])))
    protected = set(protected_variables)
    steps = []
    while True:
        eligible = (item for item in candidates(rows, live, support_cap, terminal_quadratic) if item[1] not in protected)
        choice = next(eligible, None)
        if choice is None:
            break
        row_id, variable, sign, definition = choice
        steps.append({
            "source_row_id": row_id,
            "variable_original_index": variable,
            "variable_name": equation["variables"][variable]["name"],
            "pivot_sign": sign,
            "row_before": pack(rows[row_id]),
            "restoration": pack(definition),
            "restoration_degree": max((len(m) for m in definition), default=0),
        })
        del rows[row_id]
        for other in rows:
            rows[other] = substitute(rows[other], variable, definition)
        live.remove(variable)
    used = {index for row in rows.values() for monomial in row for index in monomial}
    unused = sorted(live - used)
    retained = sorted(used)
    renaming = {old: new for new, old in enumerate(retained)}
    nonzero_ids = [index for index in sorted(rows) if rows[index]]
    residuals = [{
        "label": equation["residuals"][index]["label"],
        "terms": pack({tuple(renaming[v] for v in monomial): c
                       for monomial, c in rows[index].items()}),
    } for index in nonzero_ids]
    result = deepcopy(equation)
    result["variables"] = [deepcopy(equation["variables"][i]) for i in retained]
    result["residuals"] = residuals
    result["variant"] = equation.get("variant", "source") + ".nonnegative_affine_cap" + str(support_cap)
    if terminal_quadratic:
        result["variant"] += ".terminal_quadratic"
    _, metrics = polynomial_and_metrics(residuals, len(retained))
    result["metrics"].update(metrics)
    kinds = {}
    for variable_record in result["variables"]:
        kind = variable_record.get("kind", "unspecified")
        kinds[kind] = kinds.get(kind, 0) + 1
    if "variable_kinds" in result["metrics"]:
        result["metrics"]["variable_kinds"] = dict(sorted(kinds.items()))
    result["metrics"].update({
        "post_export_source_variables": len(equation["variables"]),
        "post_export_source_quadratic_rows": len(equation["residuals"]),
        "post_export_variables_eliminated": len(steps),
        "post_export_affine_variables_eliminated": sum(s["restoration_degree"] <= 1 for s in steps),
        "post_export_unused_variables_removed": len(unused),
        "post_export_affine_support_cap": support_cap,
        "post_export_terminal_quadratic_enabled": terminal_quadratic,
        "post_export_quadratic_variables_eliminated": sum(s["restoration_degree"] == 2 for s in steps),
    })
    certificate = {
        "schema": "nonnegative_monic_affine_elimination_v1",
        "source_equation_sha256": sha256(canonical_bytes(equation)).hexdigest(),
        "target_equation_sha256": sha256(canonical_bytes(result)).hexdigest(),
        "support_cap": support_cap,
        "maximum_restoration_degree": 2 if terminal_quadratic else 1,
        "source_variable_count": len(equation["variables"]),
        "source_row_count": len(equation["residuals"]),
        "steps": steps,
        "retained_original_indices_in_target_order": retained,
        "unused_original_indices_restored_to_zero": unused,
        "surviving_source_row_ids_in_target_order": nonzero_ids,
        "zero_source_row_ids": [index for index in sorted(rows) if not rows[index]],
        "inverse_instruction": "Insert retained coordinates and zero unused coordinates, then execute restorations in reverse step order.",
        "theorem": "The two nonnegative zero sets are in bijection after ignoring unused free coordinates; reverse restorations are nonnegative integer polynomials, and every retained residual remains quadratic.",
    }
    return result, certificate


def independent_verify(source, target, certificate):
    """Independently replay a certificate with occurrence-list expansion.

    This checker does not invoke contract(), candidates(), substitute(), mul(),
    unpack(), or pack(). It accepts a proposed sequence only after reconstructing
    each pivot and expanding all substitutions from literal coefficient lists.
    """
    require(certificate["source_equation_sha256"] == sha256(canonical_bytes(source)).hexdigest(), "source digest")
    require(certificate["target_equation_sha256"] == sha256(canonical_bytes(target)).hexdigest(), "target digest")
    require(source["domain"] == target["domain"] == "nonnegative integers", "domain mismatch")
    def collect(terms):
        out = {}
        for coeff, monomial in terms:
            key = tuple(sorted(monomial))
            out[key] = out.get(key, 0) + coeff
        return [[c, list(m)] for m, c in sorted(out.items()) if c]
    rows = {i: collect(row["terms"]) for i, row in enumerate(source["residuals"])}
    live = set(range(len(source["variables"])))
    for step in certificate["steps"]:
        rid, var = step["source_row_id"], step["variable_original_index"]
        require(rid in rows and var in live, "repeated or absent pivot")
        require(rows[rid] == step["row_before"], "pivot row mismatch")
        sign = step["pivot_sign"]
        require(sign in (-1, 1), "nonmonic pivot")
        definition = step["restoration"]
        require(len(definition) <= certificate["support_cap"], "support cap")
        require(all(isinstance(c, int) and c > 0 and len(m) <= certificate.get("maximum_restoration_degree",1) and var not in m for c, m in definition), "nonnegative polynomial restoration required")
        require(step.get("restoration_degree",1) == max((len(m) for _,m in definition), default=0), "restoration degree")
        require(all(v in live for _, m in definition for v in m), "restoration uses eliminated variable")
        expected = collect([[sign, [var]]] + [[-sign*c, m] for c,m in definition])
        require(expected == rows[rid], "pivot identity fails")
        del rows[rid]
        for other in rows:
            terms = []
            for coeff, monomial in rows[other]:
                products = [(coeff, [])]
                for index in monomial:
                    factor = definition if index == var else [[1, [index]]]
                    products = [(a*c, ma+m) for a,ma in products for c,m in factor]
                terms.extend(products)
            rows[other] = collect(terms)
            require(all(len(m) <= 2 for _,m in rows[other]), "quadratic degree lost")
        live.remove(var)
    retained = certificate["retained_original_indices_in_target_order"]
    unused = certificate["unused_original_indices_restored_to_zero"]
    require(set(retained).isdisjoint(unused) and set(retained)|set(unused) == live, "live partition")
    used = {v for terms in rows.values() for _, monomial in terms for v in monomial}
    require(set(retained) == used, "retained set mismatch")
    ids = [i for i in sorted(rows) if rows[i]]
    require(ids == certificate["surviving_source_row_ids_in_target_order"], "row ids")
    require([i for i in sorted(rows) if not rows[i]] == certificate["zero_source_row_ids"], "zero row ids")
    rename = {old:new for new,old in enumerate(retained)}
    for row, rid in zip(target["residuals"], ids):
        expected = collect([[c, [rename[v] for v in m]] for c,m in rows[rid]])
        require(row["terms"] == expected and row["label"] == source["residuals"][rid]["label"], "final residual mismatch")
    require(len(target["residuals"]) == len(ids), "final row count")
    require(target["variables"] == [source["variables"][i] for i in retained], "final variables")
    return {"verified": True, "eliminations": len(certificate["steps"]),
            "target_variables": len(retained), "target_rows": len(ids),
            "method": "independent exact stepwise polynomial substitution and nonnegativity checks"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--support-cap", type=int, default=4)
    parser.add_argument("--terminal-quadratic", action="store_true")
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    target, cert = contract(source, args.support_cap, terminal_quadratic=args.terminal_quadratic)
    receipt = independent_verify(source, target, cert)
    polynomial, metrics = polynomial_and_metrics(target["residuals"], len(target["variables"]))
    args.output.mkdir(parents=True, exist_ok=True)
    for filename, data in (("equation.json",target),("elimination_certificate.json",cert),
                           ("expanded_polynomial.json",polynomial),("VERIFICATION.json",receipt)):
        (args.output/filename).write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps(metrics | {"eliminations":len(cert["steps"]),"verified":receipt["verified"]},indent=2))


if __name__ == "__main__":
    main()
