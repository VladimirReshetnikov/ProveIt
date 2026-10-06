#!/usr/bin/env python3
"""Finite exact Gaussian-moment and independent discrete-ODE calculations.

Standard-library arithmetic in Q(sqrt(2)); no CAS and no network required.
The theorem's finite rule works at every fixed order. This executable imposes
0<=order<=8 as an explicit resource bound, and runs only when requested.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from math import comb, factorial
from typing import Sequence

from exact_matrix import ODE_POLYNOMIALS, bounded_int, cli_integer, require_equal

MAX_ORDER = 8


@dataclass(frozen=True)
class Q2:
    """a + b sqrt(2), represented by two exact rational numbers."""
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        for name in ("a", "b"):
            value = getattr(self, name)
            if type(value) not in (int, F):
                raise TypeError("Q2 coefficients must be integers or Fractions")
            object.__setattr__(self, name, F(value))

    @staticmethod
    def cast(value):
        if isinstance(value, Q2):
            return value
        if type(value) in (int, F):
            return Q2(value)
        return NotImplemented

    def __bool__(self):
        return bool(self.a or self.b)

    def __add__(self, other):
        other = Q2.cast(other)
        if other is NotImplemented:
            return NotImplemented
        return Q2(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, other):
        other = Q2.cast(other)
        if other is NotImplemented:
            return NotImplemented
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = Q2.cast(other)
        if other is NotImplemented:
            return NotImplemented
        return Q2(self.a * other.a + 2 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def inverse(self):
        denominator = self.a * self.a - 2 * self.b * self.b
        if not denominator:
            raise ZeroDivisionError("zero element of Q(sqrt(2))")
        return Q2(self.a / denominator, -self.b / denominator)

    def __truediv__(self, other):
        other = Q2.cast(other)
        if other is NotImplemented:
            return NotImplemented
        return self * other.inverse()

    def __rtruediv__(self, other):
        return self.inverse() * other

    def __pow__(self, exponent):
        if type(exponent) is not int:
            raise TypeError("Q2 exponent must be an integer")
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result, base = Q2(1), self
        while exponent:
            if exponent & 1:
                result *= base
            base *= base
            exponent //= 2
        return result

    def __str__(self):
        if not self.b:
            return str(self.a)
        radical = f"{self.b}*sqrt(2)"
        return radical if not self.a else f"{self.a} + ({radical})"

    def data(self):
        return {"rational": str(self.a), "sqrt2": str(self.b), "display": str(self)}


SQRT2 = Q2(0, 1)
ZERO = Q2()
ONE = Q2(1)


def generalized_binomial(alpha: F, k: int) -> F:
    result = F(1)
    for j in range(k):
        result *= (alpha - j) / (j + 1)
    return result


def _mul(a, b, degree):
    out = [0] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def _exp(series, degree):
    if series[0]:
        raise ValueError("formal exponential requires zero constant coefficient")
    out = [F(1)]
    for n in range(1, degree + 1):
        out.append(sum(j * series[j] * out[n - j] for j in range(1, n + 1)) / n)
    return out


def local_amplitude(order: int) -> list[F]:
    """Return h_0,...,h_order from the local Bessel amplitude H(s)."""
    bounded_int(order, "order", MAX_ORDER)
    p = [generalized_binomial(F(1, 2), j) * (-1)**j for j in range(order + 2)]
    p = [p[0]] + [p[j] + p[j - 1] for j in range(1, len(p))]
    regular = [F(0)] + [p[j + 1] + (F(1, 2) if j == 1 else 0)
                            for j in range(1, order + 1)]
    amplitude = [F(0)] * (order + 1)
    gamma = F(1)
    for k in range(order + 1):
        if k:
            gamma *= F((2 * k - 1)**2, 8 * k)
        # p^(-k-1/2)=(1-s)^(-k/2-1/4)(1+s)^(-k-1/2).
        left = [generalized_binomial(-F(k, 2) - F(1, 4), j) * (-1)**j
                for j in range(order - k + 1)]
        right = [generalized_binomial(-F(k) - F(1, 2), j)
                 for j in range(order - k + 1)]
        term = _mul(left, right, order - k)
        for j, coefficient in enumerate(term):
            amplitude[j + k] += gamma * coefficient
    return [F(value) for value in _mul(amplitude, _exp(regular, order), order)]


def _poly_add_into(target, source, scale=ONE):
    for power, coefficient in source.items():
        value = target.get(power, ZERO) + coefficient * scale
        if value:
            target[power] = value
        elif power in target:
            del target[power]


def _poly_mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            value = out.get(i + j, ZERO) + x * y
            if value:
                out[i + j] = value
            elif i + j in out:
                del out[i + j]
    return out


def gaussian_moment(power: int) -> Q2:
    """E[w^power], w=i*u/2^(1/4), with density exp(-u^2)/sqrt(pi)."""
    bounded_int(power, "power", 6 * MAX_ORDER + 6)
    if power & 1:
        return ZERO
    m = power // 2
    return SQRT2**(-m) * F((-1)**m * factorial(2 * m), 4**m * factorial(m))


def gaussian_coefficients(order: int) -> dict:
    """Compute all c_j through the requested fixed order by finite moments.

    Replace u by w=i*u/2^(1/4). Then s=sqrt(2)*e^2*(1+e*w),
    and all intermediate coefficients belong to Q(sqrt(2))[w].
    The constant 1+sqrt(2)w^2 in the raw phase is removed exactly;
    sqrt(2)w^2=-u^2. No floating point or symbolic integration is used.
    """
    bounded_int(order, "order", MAX_ORDER)
    degree = 2 * order
    raw = {power: {} for power in range(-2, degree + 1)}
    # 2/s = sqrt(2)*e^-2 sum_k (-e*w)^k.
    for k in range(degree + 3):
        _poly_add_into(raw[k - 2], {k: SQRT2 * (-1)**k})
    # -(e^-4+1)log(1-s) = sum_k s^k/k times e^-4+1.
    for k in range(1, (degree + 4) // 2 + 1):
        for j in range(k + 1):
            coefficient = SQRT2**k * F(comb(k, j), k)
            for shift in (-4, 0):
                power = 2 * k + j + shift
                if -2 <= power <= degree:
                    _poly_add_into(raw[power], {j: coefficient})
    _poly_add_into(raw[-2], {0: -2 * SQRT2})
    require_equal(raw[-2], {}, "Gaussian phase negative-square cancellation")
    require_equal(raw[-1], {}, "Gaussian phase negative-linear cancellation")
    require_equal(raw[0], {0: ONE, 2: SQRT2}, "Gaussian phase constant")
    phase = [{}] + [raw[j] for j in range(1, degree + 1)]
    exponential = [{0: ONE}]
    for n in range(1, degree + 1):
        term = {}
        for j in range(1, n + 1):
            _poly_add_into(term, _poly_mul(phase[j], exponential[n - j]), Q2(F(j, n)))
        exponential.append(term)
    h = local_amplitude(order)
    amplitude = [{} for _ in range(degree + 1)]
    for k, h_k in enumerate(h):
        for j in range(k + 1):
            power = 2 * k + j
            if power <= degree:
                _poly_add_into(amplitude[power], {j: SQRT2**k * h_k * comb(k, j)})
    moments = []
    for n in range(degree + 1):
        polynomial = {}
        for j in range(n + 1):
            _poly_add_into(polynomial, _poly_mul(amplitude[j], exponential[n - j]))
        # Explicit parity check is stronger than merely dropping odd moments.
        if any(power % 2 != n % 2 for power in polynomial):
            raise ArithmeticError(f"epsilon/w parity failed at degree {n}")
        moment = sum((coefficient * gaussian_moment(power)
                      for power, coefficient in polynomial.items()), ZERO)
        if n % 2 and moment:
            raise ArithmeticError(f"odd Gaussian coefficient did not vanish at {n}")
        moments.append(moment)
    return {"coefficients": moments[::2], "odd_moments": moments[1::2],
            "local_amplitude": h, "epsilon_degree": degree}


def _ode_basis(j: int, degree: int) -> list[Q2]:
    """Residual generated by unit c_j in the discrete ODE ansatz.

    With z=n^-1/2 and shift d, the normalized sequence term is
    z^j (1+d*z^2)^(-3/4-j/2)
       exp((2*sqrt(2)/z)*(sqrt(1+d*z^2)-1)).
    The coefficient recurrence is multiplied by z^4 before truncation.
    """
    shifted = {}
    for shift in range(-6, 2):
        exponent = [ZERO] * (degree + 1)
        for k in range(1, (degree + 1) // 2 + 1):
            power = 2 * k - 1
            if power <= degree:
                exponent[power] = 2 * SQRT2 * generalized_binomial(F(1, 2), k) * shift**k
        exponential = _exp(exponent, degree)
        shape = [ZERO] * (degree + 1)
        for k in range((degree - j) // 2 + 1):
            shape[j + 2 * k] = Q2(generalized_binomial(-F(3, 4) - F(j, 2), k) * shift**k)
        shifted[shift] = _mul(exponential, shape, degree)
    residual = [ZERO] * (degree + 1)
    for derivative, polynomial in enumerate(ODE_POLYNOMIALS):
        for power, coefficient in enumerate(polynomial):
            if not coefficient:
                continue
            shift = derivative - power
            prefactor = [ONE]
            for j0 in range(derivative):
                prefactor = _mul(prefactor, [ONE, ZERO, Q2(shift - j0)], degree)
            offset = 4 - 2 * derivative
            for k, pref in enumerate(prefactor):
                if not pref:
                    continue
                for m in range(degree + 1 - offset - k):
                    residual[m + offset + k] += coefficient * pref * shifted[shift][m]
    return [Q2.cast(value) for value in residual]


def discrete_ode_coefficients(order: int) -> dict:
    """Derive corrections independently; does not use the moment calculator.

    The ODE recurrence fixes relative corrections but not the leading scale;
    c_0=1 is supplied. This calculation does not prove asymptotic existence.
    """
    bounded_int(order, "order", MAX_ORDER)
    degree = order + 3
    basis = [_ode_basis(j, degree) for j in range(order + 1)]
    residual = basis[0][:]
    coefficients, equations = [ONE], []
    for j in range(1, order + 1):
        nonzero = [k for k, value in enumerate(basis[j]) if value]
        if not nonzero:
            raise ArithmeticError(f"no determining equation for c_{j}")
        power = nonzero[0]
        require_equal(power, j + 3, f"first residual power for c_{j}")
        for earlier in range(power):
            require_equal(residual[earlier], ZERO, f"earlier residual power {earlier}")
        slope, constant = basis[j][power], residual[power]
        coefficient = -constant / slope
        coefficients.append(coefficient)
        equations.append({"coefficient_index": j, "z_power": power,
                          "slope": slope.data(), "constant": constant.data(),
                          "solution": coefficient.data()})
        residual = [value + coefficient * basis[j][k] for k, value in enumerate(residual)]
    require_equal(residual, [ZERO] * (degree + 1), "solved ODE residual")
    return {"coefficients": coefficients, "equations": equations, "z_degree": degree}


DISPLAYED = [ONE, Q2(0, F(-17, 96)), Q2(F(6409, 9216)),
             Q2(0, F(-18114133, 13271040)), Q2(F(13052721749, 2548039680))]


def verify_symbolic(order: int = 4) -> dict:
    bounded_int(order, "order", MAX_ORDER)
    moments = gaussian_coefficients(order)
    discrete = discrete_ode_coefficients(order)
    require_equal(moments["coefficients"], discrete["coefficients"], "independent corrections")
    overlap = min(order, 4) + 1
    require_equal(moments["coefficients"][:overlap], DISPLAYED[:overlap], "displayed coefficients")
    return {"status": "PASS", "order": order, "arithmetic": "exact Q(sqrt(2)); standard library",
            "coefficients": [value.data() for value in moments["coefficients"]],
            "H_coefficients": [str(value) for value in moments["local_amplitude"]],
            "odd_epsilon_coefficients": [str(value) for value in moments["odd_moments"]],
            "discrete_ode_equations": discrete["equations"], "network_used": False}


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=cli_integer(MAX_ORDER), default=4,
                        help=f"correction order, 0..{MAX_ORDER}; default 4")
    args = parser.parse_args(argv)
    try:
        result = verify_symbolic(args.order)
    except (TypeError, ValueError, ArithmeticError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
