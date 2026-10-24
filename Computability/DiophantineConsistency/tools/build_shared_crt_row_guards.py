#!/usr/bin/env python3
"""Append only guards not eliminated by an elementary integer row closure.

The certificate uses c*x=P, c>0, with nonnegative coefficients in P.
Odd-exponent variables must already be nonnegative; even powers are
nonnegative over all integers. No power/CRT semantics enters this closure.
"""
import argparse
from collections import Counter, defaultdict, deque
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT/"candidates/shared-crt-power-slack-reduction/affine"
DEST = ROOT/"candidates/shared-crt-row-guards"
PINS = {
    "equation.json": "f47c4b3b7546f706477dd7637cf2ede4c51d96fd00dbc2796db2939d7f5f73aa",
    "expanded_polynomial.json": "f83a264ac2c58641ffb8ec0a42b8406cabac62abe084c6f294ac96182333535f",
}


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def encoded(value):
    return (json.dumps(value, separators=(",", ":"), sort_keys=True)+"\n").encode()


def rules_from_rows(rows):
    rules = []
    for index, row in enumerate(rows):
        terms = {tuple(m): c for c, m in row["terms"]}
        need(len(terms) == len(row["terms"]), "unique row terms")
        for mon, coefficient in terms.items():
            if len(mon) != 1:
                continue
            output = mon[0]
            if any(output in m for m in terms if m != mon):
                continue
            sign = 1 if coefficient > 0 else -1
            rhs = [(-sign*c, m) for m, c in terms.items() if m != mon]
            if any(c < 0 for c, m in rhs):
                continue
            required = sorted({i for c, m in rhs for i, exponent in Counter(m).items()
                               if exponent % 2})
            rules.append(dict(row=index, output=output, coefficient=abs(coefficient),
                              required_nonnegative=required))
    return rules


def close(guards, rules, count, record=False):
    known = set(guards)
    watchers = defaultdict(list)
    required = []
    for i, rule in enumerate(rules):
        deps = set(rule["required_nonnegative"])
        required.append(deps)
        for x in deps:
            watchers[x].append(i)
    queue = deque(i for i, deps in enumerate(required) if deps <= known)
    queued = set(queue)
    proof = []
    while queue:
        i = queue.popleft()
        rule = rules[i]
        if rule["output"] in known or not required[i] <= known:
            continue
        known.add(rule["output"])
        if record:
            proof.append(dict(variable=rule["output"], row=rule["row"]))
        for j in watchers[rule["output"]]:
            if j not in queued and required[j] <= known:
                queue.append(j)
                queued.add(j)
    return len(known) == count, proof


def build():
    raw = {}
    for name, pin in PINS.items():
        data = (PARENT/name).read_bytes()
        need(sha256(data).hexdigest() == pin, "frozen natural parent: "+name)
        raw[name] = json.loads(data)
    parent = raw["equation.json"]
    n = len(parent["variables"])
    semantics = {i for i, v in enumerate(parent["variables"]) if v["kind"] != "gate"}
    need(n == 3328 and len(semantics) == 1395 and len(parent["residuals"]) == 2723,
         "exact source dimensions")
    rules = rules_from_rows(parent["residuals"])
    guards = set(semantics)
    need(close(guards, rules, n)[0], "original semantic guards suffice")
    # Deterministic local deletion, not a minimum-guard claim.
    for i in sorted(semantics):
        if close(guards-{i}, rules, n)[0]:
            guards.remove(i)
    complete, proof = close(guards, rules, n, record=True)
    need(complete and len(proof)+len(guards) == n, "complete row certificate")
    variables = list(parent["variables"])
    rows = list(parent["residuals"])
    bindings = []
    polynomial = defaultdict(int, {tuple(m): c for c, m in raw["expanded_polynomial.json"]["terms"]})
    for i in sorted(guards):
        aux = list(range(len(variables), len(variables)+3))
        for suffix in ["a", "b", "c"]:
            variables.append(dict(name="rowguard."+str(i)+"."+suffix, kind="nonnegativity"))
        a, b, c = aux
        terms = sorted([[1, [i]], [-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]],
                       key=lambda term: term[1])
        rows.append(dict(label="row-derived nonnegativity seed "+str(i), terms=terms))
        bindings.append(dict(input=i, auxiliaries=aux))
        for x, m in terms:
            for y, p in terms:
                polynomial[tuple(sorted(m+p))] += x*y
    collected = [[c, list(m)] for m, c in sorted(polynomial.items()) if c]
    metrics = dict(variables=len(variables), natural_parent_variables=n,
                   original_semantic_inputs=len(semantics), semantic_inputs_guarded=len(guards),
                   semantic_guards_removed=len(semantics)-len(guards),
                   nonnegativity_auxiliaries=3*len(guards), row_certificate_steps=len(proof),
                   quadratic_rows=len(rows), exact_degree=max(len(m) for c, m in collected),
                   expanded_monomials=len(collected),
                   max_abs_expanded_coefficient=max(abs(c) for c, m in collected),
                   max_abs_row_coefficient=max(abs(c) for row in rows for c, m in row["terms"]))
    equation = dict(schema="finite_quadratic_residuals_v1", domain="unrestricted integers",
                    polynomial="sum(square(row) for row in residuals)", variables=variables,
                    residuals=rows, natural_parent_sha256=PINS["equation.json"],
                    seed_guards=bindings, metrics=metrics)
    expanded = dict(schema="sparse_integer_polynomial_v1", domain="unrestricted integers",
                    variables=len(variables), terms=collected)
    certificate = dict(schema="integer_row_nonnegativity_v1", parent_variables=n,
                       seed_variables=sorted(guards), derivation=proof,
                       rule="c*x=P with c>0 and nonnegative coefficients; odd powers require previous nonnegativity, even powers require no premise",
                       parent_equation_sha256=PINS["equation.json"],
                       available_elementary_rules=len(rules), minimum_guard_count_claim=False)
    pins = dict(parent="../shared-crt-power-slack-reduction/affine", sha256=PINS,
                arithmetic_dependency="Only the parent's exact integer row equations enter the nonnegativity certificate.")
    files = {"equation.json": encoded(equation), "expanded_polynomial.json": encoded(expanded),
             "NONNEGATIVITY.json": encoded(certificate), "PARENT_PINS.json": encoded(pins)}
    receipt = dict(status="PASS", metrics=metrics, generator_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   sha256={name: sha256(data).hexdigest() for name, data in files.items()},
                   scope="Exact natural-prefix preservation, elementary integer row certificate, fresh quadratic guards and complete quartic; no Lean/internal-ZFC derivation.")
    files["BUILD.json"] = (json.dumps(receipt, indent=2, sort_keys=True)+"\n").encode()
    return files, receipt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    files, receipt = build()
    if not args.check:
        DEST.mkdir(parents=True, exist_ok=True)
    for name, data in files.items():
        path = DEST/name
        if args.check:
            need(path.read_bytes() == data, "deterministic file: "+name)
        else:
            path.write_bytes(data)
    print(json.dumps(dict(status="PASS", check=args.check, metrics=receipt["metrics"]), indent=2))


if __name__ == "__main__":
    main()
