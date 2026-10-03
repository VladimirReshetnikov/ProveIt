"""Exact rational-tube certificates for polynomial differential equations.

Only integers and fractions are used. Acceptance is a finite arithmetic check;
its analytic interpretation is proved in the accompanying article. This module
is not a proof-assistant verification and is not an MRDP polynomial extractor.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction
from math import prod
from typing import Sequence


class CertificateError(ValueError):
    """Malformed input or failed certificate condition."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


@dataclass(frozen=True)
class Instance:
    # F_j(x) = sum(c*x**alpha)/denominator.
    polynomials: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]
    denominator: int
    initial: tuple[Fraction, ...]
    # Each row (a,b) means dot(a,x) < b, all coefficients integral.
    target: tuple[tuple[tuple[int, ...], int], ...]

    def __post_init__(self) -> None:
        d = len(self.initial)
        require(d > 0 and len(self.polynomials) == d, "dimension mismatch")
        require(type(self.denominator) is int and self.denominator > 0,
                "positive integral denominator required")
        require(all(isinstance(x, Fraction) for x in self.initial),
                "initial coordinates must be Fraction values")
        for p in self.polynomials:
            for c, alpha in p:
                require(type(c) is int and len(alpha) == d and
                        all(type(a) is int and a >= 0 for a in alpha),
                        "invalid polynomial term")
        for a, b in self.target:
            require(len(a) == d and type(b) is int and
                    all(type(v) is int for v in a), "invalid target row")

    @property
    def dimension(self) -> int:
        return len(self.initial)

    @property
    def degree(self) -> int:
        return max([1] + [sum(a) for p in self.polynomials for _, a in p])

    def bounds(self, radius: int) -> tuple[int, int]:
        m = sum(abs(c) * radius ** sum(a)
                for p in self.polynomials for c, a in p)
        ell = sum(abs(c) * sum(a) * radius ** (sum(a) - 1)
                  for p in self.polynomials for c, a in p if sum(a))
        return m, ell

    def homogeneous(self, node: Sequence[int], scale: int) -> list[int]:
        k = self.degree
        return [sum(c * prod(x ** e for x, e in zip(node, a)) *
                    scale ** (k - sum(a)) for c, a in p)
                for p in self.polynomials]

    def serializable(self) -> dict:
        return {"polynomials": self.polynomials, "denominator": self.denominator,
                "initial": [[x.numerator, x.denominator] for x in self.initial],
                "target": self.target}


@dataclass
class Certificate:
    steps: int
    inverse_step: int
    scale: int
    radius: int
    initial_error_units: int
    forcing_units: int
    nodes: list[list[int]]
    errors: list[int]
    floor_remainders: list[list[int]]
    ceiling_remainders: list[int]

    def serializable(self) -> dict:
        return asdict(self)


def generate(instance: Instance, steps: int, inverse_step: int, scale: int,
             radius: int, initial_error_units: int = 0,
             forcing_units: int = 0) -> Certificate:
    """Generate the unique candidate at fixed parameters; acceptance is separate."""
    n, h, d, r = steps, inverse_step, scale, radius
    require(all(type(v) is int and v > 0 for v in (n, h, d, r)),
            "N,H,D,R must be positive integers")
    require(all(type(v) is int and v >= 0
                for v in (initial_error_units, forcing_units)),
            "error and forcing units must be natural numbers")
    require(all(d % x.denominator == 0 for x in instance.initial),
            "scale must clear initial denominators")
    m, ell = instance.bounds(r)
    j = forcing_units
    q = instance.denominator * h * d ** (instance.degree - 1)
    b, k = h * h, h * (h + ell)
    c = ell * (d * m + j) + h * h + j * h
    nodes = [[int(d * x) for x in instance.initial]]
    errors = [initial_error_units]
    us, vs = [], []
    for _ in range(n):
        delta_u = [divmod(f, q) for f in instance.homogeneous(nodes[-1], d)]
        nodes.append([x + delta for x, (delta, _) in zip(nodes[-1], delta_u)])
        us.append([u for _, u in delta_u])
        value = k * errors[-1] + c
        error = (value + b - 1) // b
        errors.append(error)
        vs.append(b * error - value)
    return Certificate(n, h, d, r, initial_error_units, j,
                       nodes, errors, us, vs)


def verify(instance: Instance, cert: Certificate) -> dict:
    """Raise CertificateError on rejection; return exact margins on acceptance."""
    n, h, d, r = cert.steps, cert.inverse_step, cert.scale, cert.radius
    require(all(type(v) is int and v > 0 for v in (n, h, d, r)),
            "invalid positive parameters")
    require(all(type(v) is int and v >= 0 for v in
                (cert.initial_error_units, cert.forcing_units)), "invalid noise units")
    dim = instance.dimension
    require(len(cert.nodes) == n + 1 and len(cert.errors) == n + 1 and
            len(cert.floor_remainders) == n and
            len(cert.ceiling_remainders) == n, "invalid list lengths")
    require(all(len(x) == dim and all(type(t) is int for t in x)
                for x in cert.nodes), "invalid nodes")
    require(all(type(e) is int and e >= 0 for e in cert.errors), "invalid errors")
    require(all(len(u) == dim and all(type(t) is int and t >= 0 for t in u)
                for u in cert.floor_remainders), "invalid floor remainders")
    require(all(type(v) is int and v >= 0 for v in cert.ceiling_remainders),
            "invalid ceiling remainders")
    require(cert.errors[0] == cert.initial_error_units, "wrong initial radius")
    require(all(x.denominator * v == x.numerator * d
                for x, v in zip(instance.initial, cert.nodes[0])), "wrong initial point")
    m, ell = instance.bounds(r)
    j = cert.forcing_units
    q = instance.denominator * h * d ** (instance.degree - 1)
    b, k = h * h, h * (h + ell)
    c = ell * (d * m + j) + h * h + j * h
    g = d * r * h - d * m - j
    min_guard = None
    for i in range(n):
        tilde = instance.homogeneous(cert.nodes[i], d)
        for coordinate in range(dim):
            x, y = cert.nodes[i][coordinate], cert.nodes[i + 1][coordinate]
            u = cert.floor_remainders[i][coordinate]
            require(u < q and q * (y - x) + u == tilde[coordinate],
                    f"floor equation failed at {i},{coordinate}")
            guards = (g - h * cert.errors[i] - h * x,
                      g - h * cert.errors[i] + h * x)
            require(min(guards) > 0, f"tube containment failed at {i},{coordinate}")
            min_guard = min(guards) if min_guard is None else min(min_guard, *guards)
        v = cert.ceiling_remainders[i]
        require(v < b and b * cert.errors[i + 1] == k * cert.errors[i] + c + v,
                f"radius equation failed at {i}")
    margins = [d * bound - sum(a * x for a, x in zip(row, cert.nodes[-1])) -
               sum(abs(a) for a in row) * cert.errors[-1]
               for row, bound in instance.target]
    require(all(margin > 0 for margin in margins), "target containment failed")
    return {"accepted": True, "N": n, "H": h, "D": d, "R": r,
            "M": m, "L": ell, "Q": q, "E_final": cert.errors[-1],
            "final_node": cert.nodes[-1], "tube_guard_minimum": min_guard,
            "target_integer_margins": margins,
            "final_error": str(Fraction(cert.errors[-1], d)),
            "physical_time": str(Fraction(n, h))}
