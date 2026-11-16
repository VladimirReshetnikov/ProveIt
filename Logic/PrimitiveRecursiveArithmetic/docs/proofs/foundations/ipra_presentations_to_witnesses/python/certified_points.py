"""Exact finite-algebra certificates and complete rational-point enumeration.

Standard library only. This is an executable reference implementation, not an
iPRA proof checker. Soundness is proved in the accompanying paper. Every search
in the enumeration has an explicitly computed finite range. Invalid certificates
are rejected before enumeration. Matrix entries use row-vector convention:
    (v M)[j] = sum_i v[i] M[i][j].
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm, prod


class Poly:
    """Sparse rational polynomial in a specified number of variables."""

    def __init__(self, n, terms=None):
        if not isinstance(n, int) or n < 1:
            raise ValueError("A positive number of variables is required")
        self.n = n
        self.terms = {}
        for exponents, coefficient in (terms or {}).items():
            e = tuple(exponents)
            if len(e) != n or any(not isinstance(x, int) or x < 0 for x in e):
                raise ValueError("Invalid exponent vector")
            coefficient = Q(coefficient)
            if coefficient:
                self.terms[e] = coefficient

    @classmethod
    def constant(cls, n, c):
        return cls(n, {(0,) * n: Q(c)})

    @classmethod
    def variable(cls, n, k):
        if not 0 <= k < n:
            raise ValueError("Invalid variable")
        e = [0] * n
        e[k] = 1
        return cls(n, {tuple(e): Q(1)})

    def _coerce(self, other):
        if not isinstance(other, Poly):
            other = Poly.constant(self.n, other)
        if self.n != other.n:
            raise ValueError("Polynomial arity mismatch")
        return other

    def __add__(self, other):
        other = self._coerce(other)
        terms = self.terms.copy()
        for e, c in other.terms.items():
            terms[e] = terms.get(e, Q(0)) + c
        return Poly(self.n, terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        other = self._coerce(other)
        terms = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                g = tuple(a + b for a, b in zip(e, f))
                terms[g] = terms.get(g, Q(0)) + c * d
        return Poly(self.n, terms)

    __rmul__ = __mul__

    def __truediv__(self, c):
        return self * (1 / Q(c))

    def __pow__(self, k):
        if not isinstance(k, int) or k < 0:
            raise ValueError("Polynomial exponent must be a natural number")
        result = Poly.constant(self.n, 1)
        for _ in range(k):
            result = result * self
        return result

    def __eq__(self, other):
        try:
            other = self._coerce(other)
            return self.terms == other.terms
        except (ValueError, TypeError):
            return False

    def evaluate(self, point):
        if len(point) != self.n:
            raise ValueError("Point arity mismatch")
        point = tuple(map(Q, point))
        return sum((c * prod(x ** a for x, a in zip(point, e))
                    for e, c in self.terms.items()), Q(0))

    def as_json(self):
        return [{"exponents": list(e), "coefficient": str(c)}
                for e, c in sorted(self.terms.items())]


@dataclass
class Certificate:
    equations: list
    generators: list
    unit: list
    unit_witness: list
    actions: list
    witnesses: list

    @property
    def variables(self):
        return self.generators[0].n

    @property
    def dimension(self):
        return len(self.generators)


def zero_witnesses(n, d, s):
    return [[[Poly.constant(n, 0) for _ in range(s)]
             for _ in range(d)] for _ in range(n)]


def linear_combination(coefficients, polys, n):
    if len(coefficients) != len(polys):
        raise ValueError("Linear-combination length mismatch")
    return sum((a * b for a, b in zip(coefficients, polys)),
               Poly.constant(n, 0))


def check_certificate(cert):
    """Return acceptance and a specific failure reason; no algebraic oracle."""
    try:
        n, d, s = cert.variables, cert.dimension, len(cert.equations)
        if d == 0 or len(cert.unit) != d or len(cert.unit_witness) != s:
            return False, "unit dimensions"
        if len(cert.actions) != n or len(cert.witnesses) != n:
            return False, "variable dimensions"
        all_polys = cert.equations + cert.generators + cert.unit_witness
        if any(p.n != n for p in all_polys):
            return False, "polynomial arity"
        unit_residual = 1 - linear_combination(cert.unit, cert.generators, n)
        if unit_residual != linear_combination(cert.unit_witness, cert.equations, n):
            return False, "unit identity"
        for k in range(n):
            m, w = cert.actions[k], cert.witnesses[k]
            if len(m) != d or any(len(row) != d for row in m) or len(w) != d:
                return False, "matrix dimensions"
            x = Poly.variable(n, k)
            for j in range(d):
                if len(w[j]) != s or any(p.n != n for p in w[j]):
                    return False, "action witness dimensions"
                residual = x * cert.generators[j] - linear_combination(
                    [Q(m[i][j]) for i in range(d)], cert.generators, n)
                if residual != linear_combination(w[j], cert.equations, n):
                    return False, f"action identity ({k}, {j})"
        return True, "accepted"
    except (IndexError, TypeError, ValueError, ZeroDivisionError, AttributeError):
        return False, "malformed certificate"


def denominator_bounds(cert):
    """Compute (Delta, A, R) for each coordinate, assuming acceptance."""
    result = []
    for m in cert.actions:
        delta = 1
        for row in m:
            for a in row:
                delta = lcm(delta, Q(a).denominator)
        a = [[int(delta * Q(x)) for x in row] for row in m]
        r = max(sum(abs(a[i][j]) for i in range(len(a)))
                for j in range(len(a)))
        result.append({"delta": delta, "matrix": a, "radius": r})
    return result


def mixed_radix_digits(index, radices):
    if any(b < 1 for b in radices) or not 0 <= index < prod(radices):
        raise ValueError("Invalid mixed-radix input")
    digits = []
    for b in radices:
        index, digit = divmod(index, b)
        digits.append(digit)
    return digits


def enumerate_rational_zeros(cert):
    """Return all rational zeros when the certificate is valid."""
    ok, reason = check_certificate(cert)
    if not ok:
        raise ValueError("Certificate rejected: " + reason)
    bounds = denominator_bounds(cert)
    radices = [2 * b["radius"] + 1 for b in bounds]
    candidate_count = prod(radices)
    points = []
    for index in range(candidate_count):
        digits = mixed_radix_digits(index, radices)
        p = tuple(Q(digit - b["radius"], b["delta"])
                  for digit, b in zip(digits, bounds))
        if all(f.evaluate(p) == 0 for f in cert.equations):
            points.append(p)
    return {"points": points, "bounds": bounds, "candidates": candidate_count}


def primitive_evaluation_witness(cert, point):
    """Independent, inspectable arithmetic witness for each retained point."""
    v = [b.evaluate(point) for b in cert.generators]
    scale = prod(x.denominator for x in v)
    u = [int(scale * x) for x in v]
    g = 0
    for x in u:
        g = gcd(g, abs(x))
    if g == 0:
        raise ValueError("Unit identity must rule out a zero evaluation vector")
    w = [x // g for x in u]
    witness = {"primitive_vector": w, "coordinates": []}
    for x, b in zip(point, denominator_bounds(cert)):
        z = b["delta"] * x
        if z.denominator != 1 or abs(z) > b["radius"]:
            raise AssertionError("Eigenvalue grid invariant failed")
        a = b["matrix"]
        if any(sum(w[i] * a[i][j] for i in range(len(w))) != z * w[j]
               for j in range(len(w))):
            raise AssertionError("Evaluation row identity failed")
        witness["coordinates"].append({"scaled_value": int(z),
                                         "delta": b["delta"],
                                         "radius": b["radius"]})
    return witness


def companion_certificate(coefficients):
    """Construct a certificate for a supplied monic univariate polynomial."""
    coefficients = list(map(Q, coefficients))
    if len(coefficients) < 2 or coefficients[-1] != 1:
        raise ValueError("A positive-degree monic polynomial is required")
    x = Poly.variable(1, 0)
    d = len(coefficients) - 1
    f = sum((c * x ** i for i, c in enumerate(coefficients)), Poly(1))
    basis = [x ** i for i in range(d)]
    m = [[Q(0) for _ in range(d)] for _ in range(d)]
    for j in range(d - 1):
        m[j + 1][j] = Q(1)
    for i in range(d):
        m[i][-1] = -coefficients[i]
    w = zero_witnesses(1, d, 1)
    w[0][-1][0] = Poly.constant(1, 1)
    return Certificate([f], basis, [Q(1)] + [Q(0)] * (d - 1),
                       [Poly(1)], [m], w)


def certificate_as_json(cert):
    return {
        "variables": cert.variables,
        "equations": [f.as_json() for f in cert.equations],
        "generators": [b.as_json() for b in cert.generators],
        "unit": list(map(str, cert.unit)),
        "unit_witness": [h.as_json() for h in cert.unit_witness],
        "actions": [[[str(Q(a)) for a in row] for row in m] for m in cert.actions],
        "witnesses": [[[h.as_json() for h in hs] for hs in w] for w in cert.witnesses]
    }


def certificate_from_json(data):
    n = data["variables"]
    def poly(terms):
        out = Poly(n)
        for term in terms:
            out = out + Poly(n, {tuple(term["exponents"]): Q(term["coefficient"])})
        return out
    return Certificate(
        list(map(poly, data["equations"])), list(map(poly, data["generators"])),
        list(map(Q, data["unit"])), list(map(poly, data["unit_witness"])),
        [[[Q(a) for a in row] for row in m] for m in data["actions"]],
        [[[poly(h) for h in hs] for hs in w] for w in data["witnesses"]])


if __name__ == "__main__":
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", help="Certificate JSON file")
    args = parser.parse_args()
    with open(args.certificate, encoding="utf-8") as stream:
        cert = certificate_from_json(json.load(stream))
    result = enumerate_rational_zeros(cert)
    result["points"] = [list(map(str, p)) for p in result["points"]]
    print(json.dumps(result, indent=2))
