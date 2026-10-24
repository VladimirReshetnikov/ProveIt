#!/usr/bin/env python3
"""Independent integer-row certificate and complete quartic verifier.

Imports no generator, natural compiler, power graph, or closure algorithm.
Each step is reconstructed directly from one actual integer polynomial row.
"""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def verify_derivation(rows, certificate, n):
    seeds = certificate["seed_variables"]
    need(seeds == sorted(set(seeds)) and all(type(i) is int and 0 <= i < n for i in seeds),
         "valid distinct nonnegativity seeds")
    known = set(seeds)
    coefficients = Counter()
    square_terms = 0
    step_details = []
    for step in certificate["derivation"]:
        output, index = step["variable"], step["row"]
        need(type(output) is int and 0 <= output < n and output not in known, "new output")
        need(type(index) is int and 0 <= index < len(rows), "actual prefix row")
        terms = {tuple(m): c for c, m in rows[index]["terms"]}
        need((output,) in terms, "linear output term")
        c = terms[(output,)]
        need(type(c) is int and c != 0, "nonzero integer output coefficient")
        sign = 1 if c > 0 else -1
        requirements = set()
        for mon, coefficient in terms.items():
            if mon == (output,):
                continue
            need(output not in mon, "output absent from its RHS")
            need(-sign*coefficient >= 0, "nonnegative RHS coefficients")
            powers = Counter(mon)
            for variable, exponent in powers.items():
                if exponent % 2:
                    need(variable in known, "uncertified odd-power premise")
                    requirements.add(variable)
            if mon and all(exponent % 2 == 0 for exponent in powers.values()):
                square_terms += 1
        # Multiplication of the original zero row by sign gives |c|*x=P.
        # Every RHS monomial is nonnegative, hence the new x is nonnegative.
        known.add(output)
        coefficients[abs(c)] += 1
        step_details.append(dict(variable=output, row=index, positive_coefficient=abs(c),
                                 required_nonnegative=sorted(requirements)))
    need(known == set(range(n)), "every original coordinate certified")
    return dict(status="PASS", seed_count=len(seeds), certified_coordinates=len(known),
                derivation_steps=len(step_details), positive_coefficients=dict(sorted(coefficients.items())),
                domain_independent_even_monomials=square_terms)


def main():
    pins = json.loads((HERE/"PARENT_PINS.json").read_text())
    parent_path = (HERE/pins["parent"]).resolve()
    parents = {}
    for name, digest in pins["sha256"].items():
        raw = (parent_path/name).read_bytes()
        need(sha256(raw).hexdigest() == digest, "actual frozen parent: "+name)
        parents[name] = json.loads(raw)
    parent = parents["equation.json"]
    equation = json.loads((HERE/"equation.json").read_text())
    polynomial = json.loads((HERE/"expanded_polynomial.json").read_text())
    certificate = json.loads((HERE/"NONNEGATIVITY.json").read_text())
    n = len(parent["variables"])
    prefix = parent["residuals"]
    need(equation["domain"] == polynomial["domain"] == "unrestricted integers", "integer domain")
    need(equation["variables"][:n] == parent["variables"]
         and equation["residuals"][:len(prefix)] == prefix, "exact original prefix")
    need(certificate["parent_variables"] == n and
         certificate["parent_equation_sha256"] == pins["sha256"]["equation.json"], "certificate parent")
    semantics = {i for i, v in enumerate(parent["variables"]) if v["kind"] != "gate"}
    need(set(certificate["seed_variables"]) <= semantics, "seeds selected among original semantic inputs")
    derivation = verify_derivation(prefix, certificate, n)
    bindings = equation["seed_guards"]
    added = equation["residuals"][len(prefix):]
    need([g["input"] for g in bindings] == certificate["seed_variables"] and
         len(added) == len(bindings), "exact guard coverage")
    auxiliary = set()
    for binding, row in zip(bindings, added):
        i = binding["input"]
        a, b, c = binding["auxiliaries"]
        need(len({a, b, c}) == 3 and min(a, b, c) >= n and
             not ({a, b, c} & auxiliary), "fresh distinct guard auxiliaries")
        auxiliary.update([a, b, c])
        terms = {tuple(m): coefficient for coefficient, m in row["terms"]}
        need(terms == {(i,): 1, (a, a): -1, (b, b): -1, (c, c): -1, (c,): -1},
             "exact Legendre guard polynomial")
    N = len(equation["variables"])
    need(auxiliary == set(range(n, N)) and N == n+3*len(bindings), "complete variable list")
    need(len({v["name"] for v in equation["variables"]}) == N, "distinct variable names")
    collected = defaultdict(int)
    used = set()
    for row in equation["residuals"]:
        need(len({tuple(m) for c, m in row["terms"]}) == len(row["terms"]), "canonical row support")
        for c, m in row["terms"]:
            need(type(c) is int and c and len(m) <= 2 and m == sorted(m) and
                 all(type(i) is int and 0 <= i < N for i in m), "literal quadratic term")
            used.update(m)
        for c, m in row["terms"]:
            for d, p in row["terms"]:
                collected[tuple(sorted(m+p))] += c*d
    wanted = {m: c for m, c in collected.items() if c}
    actual = {tuple(m): c for c, m in polynomial["terms"]}
    need(actual == wanted and len(actual) == len(polynomial["terms"]), "complete squared system")
    need(used == set(range(N)), "all variables live")
    need(max(map(len, actual)) == 4 and actual[(N-1,)*4] == 1, "exact quartic coefficient")
    metrics = equation["metrics"]
    need(metrics["variables"] == N and metrics["quadratic_rows"] == len(equation["residuals"]) and
         metrics["expanded_monomials"] == len(actual) and
         metrics["max_abs_expanded_coefficient"] == max(map(abs, actual.values())), "metrics")
    # Controls supplement Legendre's unbounded theorem, not replace it.
    represented = {a*a+b*b+c*(c+1) for a in range(33) for b in range(33) for c in range(33)}
    need(set(range(1001)) <= represented, "three-square controls")
    receipt = dict(status="PASS", optimized=not __debug__, metrics=metrics,
                   row_certificate=derivation, full_prefix_rows=len(prefix),
                   complete_polynomial_terms=len(actual), all_variables_live=True,
                   final_auxiliary_fourth_power_coefficient=1,
                   bounded_three_square_controls=1001,
                   file_sha256={name: sha256((HERE/name).read_bytes()).hexdigest() for name in
                                ["equation.json", "expanded_polynomial.json", "NONNEGATIVITY.json"]},
                   scope="Direct arbitrary-integer row derivation, exact guards and whole quartic expansion. No natural-parent correctness is used to prove nonnegativity; no Lean/internal-ZFC derivation.")
    target = HERE/("CHECK_OPTIMIZED.json" if sys.flags.optimize else "CHECK.json")
    target.write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print("PASS every integer row certificate step, exact guard coverage and complete collected quartic")


if __name__ == "__main__":
    main()
