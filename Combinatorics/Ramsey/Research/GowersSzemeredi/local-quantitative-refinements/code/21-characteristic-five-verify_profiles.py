#!/usr/bin/env python3
"""Independent diagnostics for the characteristic-five profile lemmas.

Only Python's standard library is required. Exact monomial dictionaries
check the three sextic Fourier formulas and the septic derivative identity
on F_5. Deterministic numerical checks then exercise arbitrary and strongly
concentrated real functions on F_5 and F_5^2. Two F_5^2 cases are also
compared with direct physical-space cube sums.

These finite checks supplement the written proofs; they are not a formal
verification of the group-uniform statements.
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
from collections import Counter
from pathlib import Path


VERTICES = list(itertools.product(range(2), repeat=3))


def monomial(labels):
    """The centered coefficient a_0 is zero; a_-r is a separate variable."""
    labels = tuple(r % 5 for r in labels)
    if 0 in labels:
        return None
    return tuple(labels.count(r) for r in range(1, 5))


def add_monomial(dictionary, labels, coefficient=1):
    key = monomial(labels)
    if key is not None:
        dictionary[key] += coefficient


def support_dictionary(omitted):
    support = [v for v in VERTICES if v not in omitted]
    result = Counter()
    for labels in itertools.product(range(1, 5), repeat=len(support)):
        if sum(labels) % 5:
            continue
        if any(sum(r * v[k] for r, v in zip(labels, support)) % 5
               for k in range(3)):
            continue
        add_monomial(result, labels)
    return result


def exact_formula_checks():
    expected = [Counter(), Counter(), Counter()]
    for r, s in itertools.product(range(5), repeat=2):
        t = -r - s
        add_monomial(expected[0], (r, -r, s, -s, t, -t))
        add_monomial(expected[1], (r, -r, s, s, r - s, -r - s))
        add_monomial(expected[2], (r, r, s, s, t, t))
    omitted = [((0, 0, 0), (0, 0, 1)),
               ((0, 0, 0), (0, 1, 1)),
               ((0, 0, 0), (1, 1, 1))]
    result = []
    for name, pair, target in zip(("edge", "face_diagonal", "body_diagonal"),
                                  omitted, expected):
        actual = support_dictionary(pair)
        assert actual == target, (name, actual - target, target - actual)
        result.append({"identity": "sextic_" + name,
                       "monomials": len(actual),
                       "coefficient_sum": sum(actual.values()),
                       "passed": True})

    septic = support_dictionary(((0, 0, 0),))
    actual = Counter({key: 8 * value for key, value in septic.items()})
    target = Counter()
    for s, t, r in itertools.product(range(5), repeat=3):
        t_labels = (r, -r - s, -r - t, r + s + t)
        l_terms = ((-s, -t, s + t), (-s, s - t, t),
                   (-t, t - s, s), (-s - t, t, s))
        for l_labels in l_terms:
            # T is real under a_-r = conjugate(a_r), by a base change.
            add_monomial(target, t_labels + l_labels, 2)
    assert actual == target, ("septic", actual - target, target - actual)
    result.append({"identity": "total_septic_equals_2_inner_T_L",
                   "monomials": len(actual),
                   "coefficient_sum": sum(actual.values()),
                   "passed": True})
    return result


class Group:
    def __init__(self, dimension):
        self.dimension = dimension
        self.points = list(itertools.product(range(5), repeat=dimension))
        self.index = {x: i for i, x in enumerate(self.points)}
        self.n = len(self.points)
        self.zero = self.index[(0,) * dimension]
        self.add = [[self.index[tuple((a + b) % 5 for a, b in zip(x, y))]
                     for y in self.points] for x in self.points]
        self.neg = [self.index[tuple(-a % 5 for a in x)] for x in self.points]
        self.characters = [[cmath.exp(-2j * math.pi *
                                     sum(a * b for a, b in zip(r, x)) / 5)
                            for x in self.points] for r in self.points]

    def scale(self, k, r):
        return self.index[tuple(k * x % 5 for x in self.points[r])]

    def transform(self, f):
        a = [sum(value * phase for value, phase in zip(f, row)) / self.n
             for row in self.characters]
        # Centering is exact mathematically; remove floating roundoff here.
        a[self.zero] = 0j
        return a

    def t_array(self, a):
        add = self.add
        return [[sum(a[r] * a[add[r][s]].conjugate() *
                     a[add[r][t]].conjugate() * a[add[add[r][s]][t]]
                     for r in range(self.n))
                 for t in range(self.n)] for s in range(self.n)]


def direct_cube_statistics(group, f):
    """Three representative six-vertex sums and the seven-vertex sum."""
    n = group.n
    add = group.add
    accum = [0.0] * 4
    for x in range(n):
        for h1 in range(n):
            x1 = add[x][h1]
            for h2 in range(n):
                x2 = add[x][h2]
                x12 = add[x1][h2]
                for h3 in range(n):
                    # Vertex order: 000,001,010,011,100,101,110,111.
                    values = [f[x], f[add[x][h3]], f[x2], f[add[x2][h3]],
                              f[x1], f[add[x1][h3]], f[x12], f[add[x12][h3]]]
                    accum[0] += math.prod(values[2:])
                    accum[1] += math.prod(values[k] for k in (1, 2, 4, 5, 6, 7))
                    accum[2] += math.prod(values[1:7])
                    accum[3] += math.prod(values[1:])
    return [value / n**4 for value in accum]


def numerical_case(group, f, name, direct=False):
    n, add, neg = group.n, group.add, group.neg
    mean = sum(f) / n
    f = [x - mean for x in f]
    a = group.transform(f)
    lam = [abs(x)**2 for x in a]
    s4 = sum(x*x for x in lam)
    xi = max((r for r in range(n) if r != group.zero), key=lambda r: abs(a[r]))
    rho = abs(a[xi])
    double = group.scale(2, xi)
    b = abs(a[double])
    tail = [r for r in range(n) if r not in (xi, neg[xi])]
    d4 = sum(lam[r]**2 for r in tail)
    line = {group.scale(k, xi) for k in range(5)}
    dout = sum(lam[r]**2 for r in range(n) if r not in line)
    conv = [sum(lam[r] * lam[add[z][neg[r]]] for r in range(n)) for z in range(n)]
    energy = sum(value**2 for value in conv)
    h = sum(lam[r] * lam[s] * lam[neg[add[r][s]]]
            for r in range(n) for s in range(n))
    tarray = group.t_array(a)
    u8 = sum(abs(x)**2 for row in tarray for x in row)
    diagonal = sum(lam[r] * a[s]**2 * a[add[r][neg[s]]] * a[add[r][s]].conjugate()
                   for r in range(n) for s in range(n))
    body = sum(a[r]**2 * a[s]**2 * a[neg[add[r][s]]]**2
               for r in range(n) for s in range(n))
    c6 = 12*h + 12*diagonal + 4*body
    larray = [[2*(a[s]*a[t]*a[add[s][t]].conjugate()).real +
               2*(a[s]*a[t].conjugate()*a[add[s][neg[t]]].conjugate()).real
               for t in range(n)] for s in range(n)]
    c7 = 2*sum((tarray[s][t]*larray[s][t]).real
               for s in range(n) for t in range(n))
    b5 = sum(a[group.scale(2, r)] * a[neg[r]]**3 * a[r] for r in range(n))
    tmain = 2*(a[xi]**3*a[double]).real
    tout = sum(a[r] * a[add[r][double]].conjugate()**2 *
               a[add[add[r][double]][double]] for r in range(n) if r not in line)

    inequality_slacks = {}
    identity_errors = {}

    def leq(label, lhs, rhs):
        scale = 1 + abs(lhs) + abs(rhs)
        slack = (rhs - lhs) / scale
        assert slack >= -2e-10, (name, label, lhs, rhs, slack)
        inequality_slacks[label] = slack

    def equal(label, lhs, rhs):
        error = abs(lhs-rhs)/(1+abs(lhs)+abs(rhs))
        assert error <= 2e-10, (name, label, lhs, rhs, error)
        identity_errors[label] = error

    leq("axes_energy_bound", 2*energy-s4*s4, u8)
    leq("leading_norm_gap", 2*s4*s4, u8)
    leq("joint_norm_gap", 2*s4*s4+12*rho**4*d4+16*rho**6*b*b, u8)
    leq("tail_convolution", h, 3*math.sqrt(max(0, d4*energy)))
    leq("tail_convolution_scaled", h, (3*math.sqrt(3)/2)*math.sqrt(u8*d4))
    leq("sextic_diagonal", abs(diagonal), h)
    leq("sextic_body", abs(body), h)
    leq("total_sextic", abs(c6), 28*h)
    leq("L_square_norm", sum(abs(x)**2 for row in larray for x in row), 16*h)
    leq("total_septic", abs(c7), 8*math.sqrt(max(0, u8*h)))
    equal("off_axis_decomposition", tarray[double][double], tmain+tout)
    leq("off_axis_tail_bound", abs(tout), dout)
    phase_penalty = 4*max(abs(tmain)-dout, 0)**2
    leq("phase_norm_gap", 2*s4*s4+12*rho**4*d4+16*rho**6*b*b+phase_penalty, u8)
    if b > 1e-15:
        phase = (a[double]*a[xi].conjugate()**2).real/(b*rho*rho)
        leq("quintic_profile", b5.real, 2*rho**4*b*phase+rho*d4)

    delta = 0.31
    aw = a[:]
    aw[group.zero] = delta
    tw = group.t_array(aw)
    q = sum(abs(x)**2 for row in tw for x in row)
    expansion = delta**8+12*delta**4*s4+8*delta**3*b5+delta**2*c6+delta*c7+u8
    equal("full_centered_expansion", q, expansion)
    profile = (delta**8+12*delta**4*s4+16*delta**3*rho**2*
               (a[double]*a[xi].conjugate()**2).real+8*delta**3*rho*d4+
               42*math.sqrt(3)*delta**2*math.sqrt(u8*d4)+
               8*math.sqrt(3*math.sqrt(3)/2)*delta*u8**0.75*d4**0.25+u8)
    leq("finite_cube_profile", q, profile)
    if direct:
        raw = direct_cube_statistics(group, f)
        for label, left, right in zip(("direct_sextic_edge", "direct_sextic_diagonal",
                                      "direct_sextic_body", "direct_septic"),
                                     raw, (h, diagonal, body, c7/8)):
            equal(label, left, right)
    return {"name": name, "dimension": group.dimension, "group_order": n,
            "direct_cube_comparison": direct,
            "inequality_normalized_slacks": inequality_slacks,
            "identity_normalized_errors": identity_errors,
            "passed": True}


def run():
    rng = random.Random(20261006)
    exact = exact_formula_checks()
    cases = []
    for dimension, count in ((1, 8), (2, 12)):
        group = Group(dimension)
        for index in range(count):
            if index % 3 == 0:
                values = [rng.uniform(-1, 1) for _ in group.points]
                kind = "dense"
            else:
                theta = math.pi/10 if index % 3 == 1 else rng.uniform(-math.pi, math.pi)
                phi = 0 if index % 3 == 1 else rng.uniform(-math.pi, math.pi)
                b = 0.03 + 0.04 * rng.random()
                noise = 0.01 if index % 3 == 1 else 0.1
                values = [2*math.cos(2*math.pi*x[0]/5+theta)+
                          2*b*math.cos(4*math.pi*x[0]/5+2*theta+phi)+
                          noise*rng.uniform(-1, 1) for x in group.points]
                kind = "aligned" if index % 3 == 1 else "arbitrary_phase"
            direct = (dimension == 1 and index in (0, 1)) or (dimension == 2 and index in (0, 1))
            cases.append(numerical_case(group, values,
                                        f"F5^{dimension}_{kind}_{index}", direct))
    minimum_slacks = {}
    maximum_errors = {}
    for case in cases:
        for key, value in case["inequality_normalized_slacks"].items():
            minimum_slacks[key] = min(minimum_slacks.get(key, math.inf), value)
        for key, value in case["identity_normalized_errors"].items():
            maximum_errors[key] = max(maximum_errors.get(key, 0), value)
    return {"purpose": "Finite diagnostics supplementing the written proofs.",
            "python_dependencies": "standard library only", "seed": 20261006,
            "exact_F5_monomial_checks": exact, "numerical_case_count": len(cases),
            "direct_cube_case_count": sum(c["direct_cube_comparison"] for c in cases),
            "minimum_normalized_inequality_slacks": minimum_slacks,
            "maximum_normalized_identity_errors": maximum_errors,
            "cases": cases, "all_checks_passed": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("profile_validation_results.json"))
    args = parser.parse_args()
    results = run()
    args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"all_checks_passed": results["all_checks_passed"],
                      "exact_monomial_checks": len(results["exact_F5_monomial_checks"]),
                      "numerical_cases": results["numerical_case_count"],
                      "direct_cube_cases": results["direct_cube_case_count"],
                      "max_normalized_identity_error": max(results["maximum_normalized_identity_errors"].values()),
                      "output": str(args.output)}, indent=2))
