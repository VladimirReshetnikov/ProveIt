#!/usr/bin/env python3
"""Finite exact reference for the simple-root chart certificate producer.

The producer uses the explicit formulas in chart_producer.tex.  Evaluators are
ordinary Python callables representing *fixed* input families, not a universal
evaluator for primitive recursive programs.  Correctness requires the name,
root, inverse, and majorant hypotheses in the article.  The checks below use
72 exact Gaussian-rational instances to test the implementation; they are
finite test evidence only, not proofs of the universal theorem or iPRA
derivability.

Run: python3 code/chart_producer.py
The default report is validation/chart_producer_checks.json.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json


@dataclass(frozen=True)
class Gaussian:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other):
        return Gaussian(self.re + other.re, self.im + other.im)

    def __neg__(self):
        return Gaussian(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return Gaussian(self.re * other.re - self.im * other.im,
                        self.re * other.im + self.im * other.re)

    def scale(self, c):
        return Gaussian(c * self.re, c * self.im)

    def power(self, n):
        result = ONE
        for _ in range(n):
            result = result * self
        return result

    def norm(self):
        return abs(self.re) + abs(self.im)

    def inverse(self):
        """Exact guarded rational inverse; zero receives the total default zero."""
        denominator = self.re**2 + self.im**2
        if denominator == 0:
            return ZERO
        return Gaussian(self.re / denominator, -self.im / denominator)

    def sample(self, s):
        """Dyadic sample; the sum of component errors is at most 2^(-s-1)."""
        denominator = 2**(s + 2)
        return Gaussian(Q((self.re * denominator).__floor__(), denominator),
                        Q((self.im * denominator).__floor__(), denominator))


ZERO, ONE = Gaussian(), Gaussian(Q(1))


def gsum(xs):
    result = ZERO
    for x in xs:
        result = result + x
    return result


def ceilq(q):
    return -((-q.numerator) // q.denominator)


def producer_constants(C, B0, V, degree_x, degree_y):
    """Pure natural/rational formulas; C[(i,l)] contains integer majorants."""
    if min(B0, V, degree_x, degree_y) < 0:
        raise ValueError("Parameters must be natural numbers")
    if any(C.get((i, l), 0) < 0
           for i in range(degree_x + 1) for l in range(degree_y + 1)):
        raise ValueError("Negative coefficient majorant")
    A = B0 + 1
    M1 = sum(l * C.get((0, l), 0) * A**(l-1)
             for l in range(1, degree_y + 1))
    M2 = sum(l * (l-1) * C.get((0, l), 0) * A**(l-2)
             for l in range(2, degree_y + 1))
    Uij = {(i, j): (V+1) * sum(C.get((i, l), 0) * comb(l, j) * A**(l-j)
                              for l in range(j, degree_y + 1))
           + int(i == 0 and j == 1)
           for i in range(degree_x + 1) for j in range(max(degree_y, 1) + 1)}
    U = 1 + sum((1+j) * u for (i, j), u in Uij.items())
    h = (8 * U).bit_length()
    rho = Q(1, 2**h)
    r = 2 * h
    R = Q(1, 2**r)
    T = 1 + (V+1)*M1 + M1 + (V+1)*M2
    p = h + (8*T).bit_length()
    W = 1 + (V+1) * sum((l+1) * A**l for l in range(degree_y + 1))
    t = h + 4 + W.bit_length()
    return dict(A=A, M1=M1, M2=M2, Uij=Uij, U=U, h=h, rho=rho, r=r,
                R=R, T=T, p=p, W=W, t=t, epsilon=rho/16)


def produce_chart(C, B0, V, degree_x, degree_y, coefficient_name,
                  root_name, inverse_name):
    """Construct finite data at prescribed precisions; there is no search.

    The numerical inequalities alone are not semantic verification of arbitrary
    input names.  The article states the hypotheses under which the returned
    majorants actually enclose the represented coefficients.
    """
    data = producer_constants(C, B0, V, degree_x, degree_y)
    a, v = root_name(data["p"]), inverse_name(data["p"])
    samples = [coefficient_name(0, l, data["t"]) for l in range(degree_y + 1)]
    q0 = -(v * gsum(samples[l] * a.power(l) for l in range(degree_y + 1)))
    q1 = ONE - v * gsum((samples[l] * a.power(l-1)).scale(l)
                       for l in range(1, degree_y + 1))
    majorants = dict(data["Uij"])
    majorants[0, 0] = min(majorants[0, 0], q0.norm() + data["epsilon"])
    majorants[0, 1] = min(majorants[0, 1], q1.norm() + data["epsilon"])
    data.update(a=a, v=v, q0=q0, q1=q1, majorants=majorants)
    data.update(numerical_certificate(data, degree_x, degree_y))
    return data


def numerical_certificate(data, degree_x, degree_y):
    """Check the finite inequalities; coefficient-name validity is separate."""
    u, R, rho = data["majorants"], data["R"], data["rho"]
    A0 = sum(u[i, 0] * R**i for i in range(degree_x + 1))
    bound = sum(j*u[i, j]*R**i*rho**(j-1)
                for i in range(degree_x + 1) for j in range(1, max(degree_y, 1) + 1))
    return dict(A0=A0, Q=bound,
                numerical_conditions=bool(data["v"] != ZERO and
                                          0 < R <= 1 and 0 < rho <= 1 and
                                          A0 <= rho/2 and bound <= Q(1, 2)))


def translated_coefficients(P, a, v, degree_x, degree_y):
    """Exact coefficients of Z-v*P(X,a+Z) for a finite rational input."""
    return {(i, j): (ONE if i == 0 and j == 1 else ZERO)
            - v * gsum((P.get((i, l), ZERO) * a.power(l-j)).scale(comb(l, j))
                       for l in range(j, degree_y + 1))
            for i in range(degree_x + 1) for j in range(max(degree_y, 1) + 1)}


def validate():
    count = 0
    examples = []
    # P(0,Y)=k(Y-b)+c2(Y-b)^2, with the additional X(1+Y^2).
    # These include nonreal and negative roots, nonreal inverses, and zero
    # and signed quadratic terms.  No floating-point approximation is used.
    for br, bi, kr, ki, c2 in product(
            [Q(-2, 3), Q(0), Q(5, 4)], [Q(0), Q(1, 3)],
            [Q(-2), Q(1, 2)], [Q(0), Q(2, 5)], [Q(-1, 3), Q(0), Q(2)]):
        b, k = Gaussian(br, bi), Gaussian(kr, ki)
        w = k.inverse()
        P = {(0, 0): -(k*b) + b.power(2).scale(c2),
             (0, 1): k-b.scale(2*c2), (0, 2): Gaussian(c2),
             (1, 0): ONE, (1, 2): ONE}
        assert gsum(P.get((0, l), ZERO) * b.power(l) for l in range(3)) == ZERO
        derivative = gsum((P.get((0, l), ZERO) * b.power(l-1)).scale(l)
                          for l in range(1, 3))
        assert derivative * w == ONE
        C = {(i, l): ceilq(P.get((i, l), ZERO).norm())
             for i in range(2) for l in range(3)}
        B0, V = ceilq(b.norm()), ceilq(w.norm())
        name = lambda i, l, s: P.get((i, l), ZERO).sample(s)
        result = produce_chart(C, B0, V, 1, 2, name, b.sample, w.sample)
        actual = translated_coefficients(P, result["a"], result["v"], 1, 2)
        rho = result["rho"]
        assert result["v"] != ZERO
        assert (result["a"]-b).norm() <= Q(1, 2**result["p"])
        assert (result["v"]-w).norm() <= Q(1, 2**result["p"])
        assert actual[0, 0].norm() <= rho/8 and actual[0, 1].norm() <= rho/8
        assert all(actual[index].norm() <= result["Uij"][index] for index in actual)
        assert (result["q0"]-actual[0, 0]).norm() <= result["epsilon"]
        assert (result["q1"]-actual[0, 1]).norm() <= result["epsilon"]
        assert all(actual[index].norm() <= result["majorants"][index] for index in actual)
        assert result["majorants"][0, 0] <= rho/4
        assert result["majorants"][0, 1] <= rho/4
        assert result["numerical_conditions"]
        count += 1
        if len(examples) < 3:
            examples.append({"b": [str(b.re), str(b.im)], "inverse": [str(w.re), str(w.im)],
                             "h": result["h"], "r": result["r"],
                             "root_sample_precision": result["p"],
                             "coefficient_sample_precision": result["t"],
                             "R": str(result["R"]), "rho": str(rho),
                             "A0": str(result["A0"]), "Q": str(result["Q"])})
    return {"status": "passed", "gaussian_rational_cases": count,
            "scope": "Finite exact test evidence only; not a proof of the universal producer or iPRA derivability.",
            "arithmetic": "Gaussian pairs of Python fractions.Fraction; no floating point",
            "checks_in_every_case": ["exact root and inverse premises", "prescribed sample errors",
                                     "small F00 and F01", "all coarse coefficient bounds",
                                     "two sampled enclosure errors", "all produced majorants",
                                     "nonzero rational inverse", "both contraction inequalities"],
            "examples": examples}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent /
                        "validation" / "chart_producer_checks.json")
    args = parser.parse_args()
    report = validate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "gaussian_rational_cases": report["gaussian_rational_cases"],
                      "report": str(args.output)}, indent=2))
