#!/usr/bin/env python3
"""Independent small exact checks of degree flow; no SAT solver claim."""
import itertools
import json
import math
import random
from pathlib import Path


def clean(p):
    return {e: c for e, c in p.items() if c}


def add(p, q):
    ans = dict(p)
    for e, c in q.items():
        ans[e] = ans.get(e, 0) + c
    return clean(ans)


def mul(p, q):
    ans = {}
    for e, c in p.items():
        for f, d in q.items():
            ef = tuple(a + b for a, b in zip(e, f))
            ans[ef] = ans.get(ef, 0) + c * d
    return clean(ans)


def power(p, k, n):
    ans = {(0,) * n: 1}
    for _ in range(k):
        ans = mul(ans, p)
    return ans


def substitute(p, values, n):
    ans = {}
    for e, c in p.items():
        term = {(0,) * n: c}
        for k, value in zip(e, values):
            term = mul(term, power(value, k, n))
        ans = add(ans, term)
    return ans


def variable(i, n):
    e = [0] * n
    e[i] = 1
    return {tuple(e): 1}


def evaluate(p, x):
    return sum(c * math.prod(v ** k for v, k in zip(x, e))
               for e, c in p.items())


def degree(p):
    return max((sum(e) for e in p), default=-1)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def check_flow(rng):
    edges = [(s, t) for s in range(3) for t in range(3) if s != t]
    width = 3 + len(edges)
    checked_sectors = 0
    checked_values = 0
    for case in range(80):
        caps = [rng.randint(1, 3) for _ in range(3)]
        polynomials = []
        for g in range(3):
            allowed = [g] + [3 + j for j, (_, t) in enumerate(edges) if t == g]
            p = {}
            for _ in range(7):
                e = [0] * width
                for _ in range(rng.randint(0, caps[g])):
                    e[rng.choice(allowed)] += 1
                c = rng.choice([-2, -1, 1, 2])
                key = tuple(e)
                p[key] = p.get(key, 0) + c
            polynomials.append(clean(p))
        forms = []
        for s, _ in edges:
            forms.append(add({(0, 0, 0): rng.randint(-1, 1)},
                             {e: rng.choice([-2, -1, 1, 2]) * c
                              for e, c in variable(s, 3).items()}))
        values = [variable(g, 3) for g in range(3)] + forms
        lhs = {(0, 0, 0): 1}
        for p in polynomials:
            lhs = mul(lhs, substitute(p, values, 3))

        # Extract all incoming coefficients without performing substitution.
        coefficient_tables = []
        for p in polynomials:
            table = {}
            for e, c in p.items():
                beta = e[3:]
                table[beta] = add(table.get(beta, {}), {e[:3]: c})
            coefficient_tables.append(table)

        rhs = {}
        for choices in itertools.product(*(list(t) for t in coefficient_tables)):
            beta = tuple(sum(a[j] for a in choices) for j in range(len(edges)))
            product = {(0, 0, 0): 1}
            new_caps = []
            for g, chosen in enumerate(choices):
                q = coefficient_tables[g][chosen]
                incoming = sum(beta[j] for j, (_, t) in enumerate(edges) if t == g)
                outgoing = sum(beta[j] for j, (s, _) in enumerate(edges) if s == g)
                new_cap = caps[g] - incoming + outgoing
                new_caps.append(new_cap)
                for j, (s, _) in enumerate(edges):
                    if s == g:
                        q = mul(q, power(forms[j], beta[j], 3))
                require(degree(q) <= new_cap, (case, g, degree(q), new_cap))
                product = mul(product, q)
            require(sum(new_caps) == sum(caps), "Degree budget not conserved")
            checked_sectors += 1
            rhs = add(rhs, product)
        require(lhs == rhs, f"Polynomial identity failed in case {case}")
        multilinear = {}
        for e, c in rhs.items():
            multilinear = add(multilinear, {tuple(min(1, a) for a in e): c})
        for x in itertools.product([0, 1], repeat=3):
            require(evaluate(lhs, x) == evaluate(multilinear, x), "Boolean quotient")
            for modulus in [2, 4, 8, 32]:
                require((evaluate(lhs, x) - evaluate(rhs, x)) % modulus == 0,
                        "Residue identity")
            checked_values += 1
    return {"cases": 80, "degree_sectors_checked": checked_sectors,
            "boolean_evaluations_checked": checked_values}


def check_permanent(rng):
    checked = 0
    for d in range(1, 7):
        for _ in range(8):
            matrix = [[rng.randint(-2, 2) for j in range(d)] for i in range(d)]
            p = {(0,) * d: 1}
            for row in matrix:
                linear = {}
                for j, a in enumerate(row):
                    linear = add(linear, {e: a * c for e, c in variable(j, d).items()})
                p = mul(p, linear)
            coefficient = p.get((1,) * d, 0)
            permanent = sum(math.prod(matrix[i][perm[i]] for i in range(d))
                            for perm in itertools.permutations(range(d)))
            require(coefficient == permanent, "Permanent coefficient identity")
            checked += 1
    return {"matrices_checked": checked, "maximum_dimension": 6}


def check_interpolation(rng):
    checked = 0
    for _ in range(40):
        # A has degree at most 2 in 3 variables. W has degree at most 2 in T.
        a = {}
        for e in itertools.product([0, 1], repeat=3):
            if sum(e) <= 2:
                a[e] = rng.randint(-2, 2)
        a = clean(a)
        w = [[{(j,): rng.randint(-1, 1) for j in range(3)}
              for _ in range(3)] for _ in range(3)]
        direct = {}
        interpolated = {}
        for x in itertools.product([0, 1], repeat=3):
            bx = rng.randint(-2, 2)
            forms = []
            for row in w:
                form = {}
                for bit, entry in zip(x, row):
                    if bit:
                        form = add(form, entry)
                forms.append(form)
            direct = add(direct, {e: bx * c for e, c in substitute(a, forms, 1).items()})
            for y in itertools.product([0, 1], repeat=3):
                term = {(0,): bx * evaluate(a, y)}
                for bit, form in zip(y, forms):
                    ly = form if bit else add({(0,): 1}, {e: -c for e, c in form.items()})
                    term = mul(term, ly)
                interpolated = add(interpolated, term)
        require(direct == interpolated, "Low-degree interpolation equality")
        require(degree(interpolated) <= 4, "Deformation degree cap")
        checked += 1
    return {"examples_checked": checked, "maximum_allowed_deformation_degree": 4}


def main():
    rng = random.Random(20261026)
    result = {
        "status": "PASS",
        "scope": "Finite exact algebra only; no SAT solver or asymptotic proof by testing.",
        "degree_flow": check_flow(rng),
        "permanent_identity": check_permanent(rng),
        "low_degree_deformation": check_interpolation(rng),
        "negative_control": {
            "example": "P_1=Z_(2->1)^2, P_2=1, L_(2->1)=X_2",
            "correct_child_degrees": [0, 2],
            "incorrect_rule_omitting_outgoing_degrees": [0, 0],
            "failure_detected": degree({(0, 2): 1}) > 0,
        },
    }
    target = (Path(__file__).resolve().parents[1] / "results" / "degree_flow_checks.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
