#!/usr/bin/env python3
"""Turn a nonnegative quadratic system into an unrestricted integer quartic.

Each original variable x_i is retained and receives three fresh unrestricted
integer coordinates with the guard 8*x_i+1-a_i^2-b_i^2-c_i^2=0.
Legendre's three-square theorem proves that this guard is soluble exactly
when the original integer coordinate is nonnegative. No coefficients are
implicit: the JSON residuals and fully expanded sum of squares are emitted.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_terms(terms):
    values = {}
    for coefficient, monomial in terms:
        require(isinstance(coefficient, int), "noninteger coefficient")
        key = tuple(sorted(monomial))
        values[key] = values.get(key, 0) + coefficient
    return [[coefficient, list(key)] for key, coefficient in sorted(values.items()) if coefficient]


def expand_sos(residuals):
    values = {}
    for row in residuals:
        terms = row["terms"]
        for c, m in terms:
            for d, n in terms:
                key = tuple(sorted(m + n))
                values[key] = values.get(key, 0) + c*d
    return [[coefficient, list(key)] for key, coefficient in sorted(values.items()) if coefficient]


def make_integer(source):
    require(source["domain"] == "nonnegative integers", "source must quantify nonnegative integers")
    n = len(source["variables"])
    require(n > 0, "empty source variable list")
    require(all(len(m) <= 2 and all(0 <= i < n for i in m)
                for row in source["residuals"] for _, m in row["terms"]),
            "source is not a valid quadratic residual system")
    target = deepcopy(source)
    target["domain"] = "unrestricted integers"
    target["variant"] = source.get("variant", "source") + ".integer_three_square_guards"
    target["variables"] = deepcopy(source["variables"])
    target["residuals"] = deepcopy(source["residuals"])
    guards = []
    for i, record in enumerate(source["variables"]):
        indices = [n+3*i+j for j in range(3)]
        for suffix, index in zip(("a", "b", "c"), indices):
            require(index == len(target["variables"]), "guard coordinate allocation")
            target["variables"].append({
                "name": "nonnegative_guard."+str(i)+"."+suffix,
                "kind": "integer_sign_guard",
            })
        row = {"label": "nonnegative_guard."+str(i),
               "terms": canonical_terms([[8,[i]],[1,[]]] + [[-1,[a,a]] for a in indices])}
        guards.append({"original_index":i,"original_name":record["name"],
                       "guard_indices":indices,"residual_index":len(target["residuals"])})
        target["residuals"].append(row)
    terms = expand_sos(target["residuals"])
    polynomial = {"schema":"sparse_integer_polynomial_v1", "domain":"unrestricted integers",
                  "variables":4*n,"terms":terms}
    metrics = {
        "variables":4*n,
        "quadratic_rows":len(target["residuals"]),
        "exact_degree":max(len(m) for _,m in terms),
        "expanded_monomials":len(terms),
        "max_abs_expanded_coefficient":max(abs(c) for c,_ in terms),
        "max_abs_row_coefficient":max(abs(c) for row in target["residuals"] for c,_ in row["terms"]),
        "variable_kinds":dict(sorted(Counter(v.get("kind","unspecified") for v in target["variables"]).items())),
        "source_natural_variables":n,
        "source_quadratic_rows":len(source["residuals"]),
        "three_square_guards":n,
        "fresh_integer_guard_variables":3*n,
    }
    target["metrics"] = metrics
    target["domain_conversion"] = {
        "formula":"8*x_i+1 = a_i^2+b_i^2+c_i^2",
        "source_domain":"nonnegative integers",
        "theorem":"Legendre's three-square theorem; 8*x_i+1 is 1 modulo 8 when x_i>=0.",
        "projection":"Discard all guard variables; retained original coordinates are nonnegative at every zero.",
    }
    certificate = {
        "schema":"nonnegative_to_integer_three_square_v1",
        "source_equation_sha256":sha256(canonical_bytes(source)).hexdigest(),
        "target_equation_sha256":sha256(canonical_bytes(target)).hexdigest(),
        "expanded_polynomial_sha256":sha256(canonical_bytes(polynomial)).hexdigest(),
        "original_variable_count":n,
        "original_residual_count":len(source["residuals"]),
        "guards":guards,
        "exact_degree_certificate":{"monomial":[n,n,n,n],"coefficient":1},
        "existence_equivalence":"target has an unrestricted integer zero iff source has a nonnegative integer zero",
    }
    return target, polynomial, certificate


def independent_verify(source, target, polynomial, certificate):
    """Check by a separate symmetric expansion and closed-form guard squares."""
    require(source["domain"] == "nonnegative integers", "source domain")
    require(target["domain"] == polynomial["domain"] == "unrestricted integers", "target domain")
    require(certificate["source_equation_sha256"] == sha256(canonical_bytes(source)).hexdigest(), "source digest")
    require(certificate["target_equation_sha256"] == sha256(canonical_bytes(target)).hexdigest(), "target digest")
    require(certificate["expanded_polynomial_sha256"] == sha256(canonical_bytes(polynomial)).hexdigest(), "polynomial digest")
    n, rowcount = len(source["variables"]), len(source["residuals"])
    require(certificate["original_variable_count"] == n and certificate["original_residual_count"] == rowcount, "source counts")
    require(len(target["variables"]) == polynomial["variables"] == 4*n, "target variable count")
    require(target["variables"][:n] == source["variables"], "source variables changed")
    require(target["residuals"][:rowcount] == source["residuals"], "source residuals changed")
    require(len(target["residuals"]) == rowcount+n, "target residual count")
    require(len(certificate["guards"]) == n, "guard count")
    result = Counter()
    for row in source["residuals"]:
        terms = row["terms"]
        for i,(c,m) in enumerate(terms):
            result[tuple(sorted(m+m))] += c*c
            for d,k in terms[:i]:
                result[tuple(sorted(m+k))] += 2*c*d
    for i in range(n):
        a,b,c = n+3*i,n+3*i+1,n+3*i+2
        entry = certificate["guards"][i]
        require(entry == {"original_index":i,"original_name":source["variables"][i]["name"],
                          "guard_indices":[a,b,c],"residual_index":rowcount+i}, "guard coordinate binding")
        expected = [[1,[]],[8,[i]],[-1,[a,a]],[-1,[b,b]],[-1,[c,c]]]
        require(target["residuals"][rowcount+i] == {"label":"nonnegative_guard."+str(i),"terms":expected}, "literal guard residual")
        for suffix,v in zip(("a","b","c"),(a,b,c)):
            require(target["variables"][v] == {"name":"nonnegative_guard."+str(i)+"."+suffix,"kind":"integer_sign_guard"}, "guard variable metadata")
        # Exact independent expansion of (8*x+1-a^2-b^2-c^2)^2.
        result[()] += 1
        result[(i,)] += 16
        result[(i,i)] += 64
        for v in (a,b,c):
            result[(v,v,v,v)] += 1
            result[(v,v)] -= 2
            result[(i,v,v)] -= 16
        result[(a,a,b,b)] += 2
        result[(a,a,c,c)] += 2
        result[(b,b,c,c)] += 2
    expected_terms = [[v,list(k)] for k,v in sorted(result.items()) if v]
    require(polynomial["terms"] == expected_terms, "expanded polynomial mismatch")
    require(result[(n,n,n,n)] == 1, "exact quartic degree certificate")
    measured = {"variables":4*n,"quadratic_rows":rowcount+n,"exact_degree":4,
                "expanded_monomials":len(expected_terms),
                "max_abs_expanded_coefficient":max(abs(c) for c,_ in expected_terms),
                "max_abs_row_coefficient":max(abs(c) for r in target["residuals"] for c,_ in r["terms"])}
    for key,value in measured.items():
        require(target["metrics"][key] == value, "metric mismatch: "+key)
    return {"verified":True,"method":"independent symmetric expansion plus closed-form guard-square expansion",
            "metrics":measured,"mathematical_dependency":"Legendre's three-square theorem",
            "degree_witness":{"monomial":[n,n,n,n],"coefficient":1}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source",type=Path)
    parser.add_argument("output",type=Path)
    args = parser.parse_args()
    source = json.loads(args.source.read_text())
    target, polynomial, certificate = make_integer(source)
    receipt = independent_verify(source,target,polynomial,certificate)
    args.output.mkdir(parents=True,exist_ok=True)
    for name,data in (("equation.json",target),("expanded_polynomial.json",polynomial),
                      ("conversion_certificate.json",certificate),("VERIFICATION.json",receipt)):
        (args.output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__ == "__main__":
    main()
