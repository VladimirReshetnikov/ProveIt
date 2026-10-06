#!/usr/bin/env python3
"""Report148 exact finite checks; Python standard library only.

All arithmetic used to establish a check is integral or rational.  The symbolic
algebra and finite fixtures are not proofs of analytic uniformity, infinite
atom bounds, eventual onset, or exact-ratio monotonicity.  Written afresh for
Report148 from the displayed mathematical identities, not from Report147 code.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
import os
from math import comb, factorial
from pathlib import Path

RESIDUES = (0, 2, 1)
NORMALIZERS = (Q(1), Q(3, 2), Q(1))
SERIES_KEYS = ((0, 0), (1, 0), (2, 0), (0, 1))


def require(condition, message):
    """A check that remains active with Python's -O option."""
    if not condition:
        raise ValueError(message)


def validate_weights(weights, epsilon):
    require(epsilon in (-1, 1), "epsilon must be -1 or +1")
    require(len(weights) >= 1 and weights[0] == 0, "weights[0] must be zero")


def divisor_recurrence(weights, epsilon):
    """A_n from n A_n=sum_d B_d A_(n-d); the weights never change mid-row."""
    validate_weights(weights, epsilon)
    nmax = len(weights) - 1
    b = [Q(0) for _ in weights]
    for j in range(1, nmax + 1):
        for k in range(1, nmax // j + 1):
            b[j * k] += epsilon ** (k - 1) * j * weights[j]
    row = [Q(1)]
    for n in range(1, nmax + 1):
        row.append(sum((b[d] * row[n - d] for d in range(1, n + 1)), Q(0)) / n)
    return row


def factor_coefficients(weight, epsilon, degree):
    """[y^k](1-epsilon*y)^(-epsilon*weight), by generalized binomials."""
    require(epsilon in (-1, 1), "epsilon must be -1 or +1")
    values = [Q(1)]
    for k in range(1, degree + 1):
        values.append(values[-1] * (weight + epsilon * (k - 1)) / k)
    return values


def profile_convolution(weights, epsilon):
    """Independent finite Euler product via its individual binomial factors."""
    validate_weights(weights, epsilon)
    nmax = len(weights) - 1
    row = [Q(1)] + [Q(0)] * nmax
    for j in range(1, nmax + 1):
        factor = factor_coefficients(Q(weights[j]), epsilon, nmax // j)
        result = [Q(0)] * (nmax + 1)
        for n, value in enumerate(row):
            for k in range((nmax - n) // j + 1):
                result[n + j * k] += value * factor[k]
        row = result
    return row


def normalized_log_atom_profile(m, r, t, x0, epsilon):
    """Finite exact right side of the normalized logarithmic-atom identity.

    Only (j,k)=(3,1) is excluded. Core collisions (3,k>=2), pure collisions,
    and every atom of degree <=3m+r remain in this independent convolution.
    """
    require(r in (0, 1, 2), "r must be 0, 1, or 2")
    require(epsilon in (-1, 1), "epsilon must be -1 or +1")
    nmax = 3 * m + r
    profile = [Q(1)] + [Q(0)] * nmax
    for j in range(1, nmax + 1):
        for k in range(1, nmax // j + 1):
            if (j, k) == (3, 1):
                continue
            degree = j * k
            activity = Q(epsilon ** (k - 1) * j ** t, k) * x0 ** degree
            updated = [Q(0)] * (nmax + 1)
            atom_factor = [Q(1)]
            for count in range(1, nmax // degree + 1):
                atom_factor.append(atom_factor[-1] * activity / count)
            for n, value in enumerate(profile):
                for count in range((nmax - n) // degree + 1):
                    updated[n + count * degree] += value * atom_factor[count]
            profile = updated
    return sum((profile[degree] * falling_ratio(m, (degree - r) // 3)
                for degree in range(r, nmax + 1, 3)), Q(0))


def integer_weights(nmax, t):
    require(isinstance(t, int) and t >= 0, "this exact evaluator needs integer t >= 0")
    return [Q(0)] + [Q(j ** t) for j in range(1, nmax + 1)]


def wrong_diagonal_recurrence(nmax, epsilon):
    """Deliberately WRONG: freezes t at each new n, but reuses old diagonal entries.

    This negative fixture must differ from A(n,n).  It is never used as an
    evaluator for the Euler product.
    """
    row = [Q(1)]
    for n in range(1, nmax + 1):
        b = [Q(0)] * (n + 1)
        for j in range(1, n + 1):
            for k in range(1, n // j + 1):
                b[j * k] += epsilon ** (k - 1) * j ** (n + 1)
        row.append(sum((b[d] * row[n - d] for d in range(1, n + 1)), Q(0)) / n)
    return row


def h_by_recurrence(nmax):
    """H_k=[u^k] exp(u+u^2), from k H_k=H_(k-1)+2 H_(k-2)."""
    h = [Q(1)]
    for k in range(1, nmax + 1):
        h.append((h[k - 1] + (2 * h[k - 2] if k > 1 else 0)) / k)
    return h


def h_by_profiles(k):
    return sum((Q(1, factorial(k - 2 * j) * factorial(j)) for j in range(k // 2 + 1)), Q(0))


def falling_ratio(m, ell):
    require(isinstance(m, int) and m >= 1, "m must be a positive integer")
    require(isinstance(ell, int) and ell >= 0, "ell must be a nonnegative integer")
    if ell > m:
        return Q(0)
    result = Q(1)
    for j in range(ell):
        result *= Q(m - j, m)
    return result


def pure_profile_coefficients(m, r):
    """Polynomial numerator sum H_K a^K P_((2K-r)/3), by N2,N4 profiles."""
    require(r in (0, 1, 2), "r must be 0, 1, or 2")
    result = {}
    n = 3 * m + r
    for n4 in range(n // 4 + 1):
        for n2 in range((n - 4 * n4) // 2 + 1):
            degree = 2 * n2 + 4 * n4
            if degree % 3 == r:
                ell = (degree - r) // 3
                k = n2 + 2 * n4
                coefficient = falling_ratio(m, ell) / (factorial(n2) * factorial(n4))
                result[k] = result.get(k, Q(0)) + coefficient
    return result


def pure_filtered_coefficients(m, r):
    result = {}
    for k in range(RESIDUES[r], (3 * m + r) // 2 + 1, 3):
        ell = (2 * k - r) // 3
        result[k] = h_by_profiles(k) * falling_ratio(m, ell)
    return result


class Laurent:
    """Tiny exact Laurent polynomial ring Q[x,x^-1,w,w^-1]."""
    def __init__(self, terms=None):
        if isinstance(terms, (int, Q)):
            terms = {(0, 0): Q(terms)}
        self.terms = {key: Q(value) for key, value in (terms or {}).items() if value}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Laurent) else Laurent(value)

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for key, value in other.terms.items():
            terms[key] = terms.get(key, Q(0)) + value
        return Laurent(terms)

    __radd__ = __add__

    def __neg__(self):
        return Laurent({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        terms = {}
        for (a, b), c in self.terms.items():
            for (d, e), f in other.terms.items():
                key = (a + d, b + e)
                terms[key] = terms.get(key, Q(0)) + c * f
        return Laurent(terms)

    __rmul__ = __mul__

    def __truediv__(self, value):
        return self * (Q(1) / value)

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "only nonnegative integer powers")
        result = Laurent(1)
        for _ in range(power):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def encode(self):
        return [{"x": i, "w": j, "coefficient": str(c)} for (i, j), c in sorted(self.terms.items())]


X = Laurent({(1, 0): 1})
W = Laurent({(0, 1): 1})


def monomial(x=0, w=0, coefficient=1):
    return Laurent({(x, w): coefficient})


class Series:
    """Q[x^+-1,w^+-1][u,v]/(u^3,uv,v^2), with exact arithmetic.

    The quotient is an algebraic bookkeeping device.  Discarding its ideal is
    analytically justified in the report by beta>5/8, not by this class.
    """
    def __init__(self, terms=None):
        if isinstance(terms, (int, Q, Laurent)):
            terms = {(0, 0): Laurent.coerce(terms)}
        self.terms = {key: Laurent.coerce(value) for key, value in (terms or {}).items()
                      if key in SERIES_KEYS and Laurent.coerce(value) != 0}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Series) else Series(value)

    def __add__(self, other):
        other = self.coerce(other)
        result = dict(self.terms)
        for key, value in other.terms.items():
            result[key] = result.get(key, Laurent()) + value
        return Series(result)

    __radd__ = __add__

    def __neg__(self):
        return Series({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        result = {}
        for (a, b), c in self.terms.items():
            for (d, e), f in other.terms.items():
                key = (a + d, b + e)
                if key in SERIES_KEYS:
                    result[key] = result.get(key, Laurent()) + c * f
        return Series(result)

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def coefficient(self, u=0, v=0):
        return self.terms.get((u, v), Laurent())

    def unit_power(self, exponent):
        require(self.coefficient() == 1, "unit_power requires constant term 1")
        h = self - 1
        p = Q(exponent)
        return 1 + h * p + h * h * (p * (p - 1) / 2)

    def unit_log(self):
        require(self.coefficient() == 1, "unit_log requires constant term 1")
        h = self - 1
        return h - h * h * Q(1, 2)


U = Series({(1, 0): 1})
V = Series({(0, 1): 1})


def pure_polynomial_identities(r):
    """a is represented by x.  Polynomial identities hold for arbitrary a."""
    a = X
    mean = (4 * a ** 2 + 2 * a - r) / 3
    variance = (16 * a ** 2 + 4 * a) / 9
    x_mean = (2 * a - r) / 3
    x_second = variance + x_mean ** 2
    first_log = -(mean * (mean - 1) + variance) / 2
    second_log = (mean - Q(1, 2)) ** 2 * variance / 2 - mean ** 3 / 6
    return {"mean_X": x_mean, "second_X": x_second,
            "first_log_numerator": first_log,
            "second_log_numerator": second_log}


def inverse_identities(r):
    """x=s0^(1/3), w=s0^p; coefficients are universal polynomials."""
    c1 = -Q(3, 4) * X ** 2
    c2 = Q(3 * (4 * r + 1), 32) * X + X ** 5
    cb = Q(27, 32) * monomial(-1, 1)
    relative = Series(1) + U * (c1 * monomial(-3)) + U * U * (c2 * monomial(-3)) + V * (cb * monomial(-3))
    model = (relative.unit_power(Q(4, 3)) * (-Q(8, 9) * X ** 4)
             + relative * U * (-Q(8, 9) * X ** 3)
             + (relative.unit_power(Q(2, 3)) * (Q(4 * (r - 1), 9) * X ** 2)
                + relative.unit_power(2) * (Q(32, 27) * X ** 6)) * U * U
             + V * W)
    log_relative = relative.unit_log()
    return {"c1": c1, "c2": c2, "cb": cb, "log_model": model,
            "minus_L_times_t_correction": log_relative,
            "relative_s": relative}


def exp_negative_bounds(value, terms=12):
    """Rigorous rational bounds on exp(-value) for rational value>=0.

    Range reduction followed by the alternating Taylor series on [0,1] and
    repeated squaring.  No binary floating point or transcendental library.
    """
    x = Q(value)
    require(x >= 0, "exponent magnitude must be nonnegative")
    require(terms >= 2 and terms % 2 == 0, "terms must be a positive even integer")
    squarings = 0
    while x > 1:
        x /= 2
        squarings += 1
    term = Q(1)
    upper = Q(1)
    for k in range(1, terms + 1):
        term *= -x / k
        upper += term
    lower = upper + term * (-x) / (terms + 1)
    require(0 <= lower <= upper <= 1, "invalid alternating-series enclosure")
    for _ in range(squarings):
        lower *= lower
        upper *= upper
    return lower, upper


def falling_global_bound_check(m, ell):
    """Certify one finite instance of the globally stated second-order bound.

    |P_l-exp[-l(l-1)/(2m)]*(1-y)| <= 9*(l^4/m^3+l^6/m^4).
    A coarse rational envelope is used whenever it already suffices.
    """
    p = falling_ratio(m, ell)
    y = Q(ell * (ell - 1) * (2 * ell - 1), 12 * m * m)
    rhs = 9 * (Q(ell ** 4, m ** 3) + Q(ell ** 6, m ** 4))
    if ell <= 1:
        return p == 1 and y == 0
    if 2 + y <= rhs:
        return True  # P and exp(-x) are both in [0,1].
    lower, upper = exp_negative_bounds(Q(ell * (ell - 1), 2 * m))
    certified_lhs = max(abs(p - lower * (1 - y)), abs(p - upper * (1 - y)))
    return certified_lhs <= rhs


def rational_witnesses():
    """Exact comparisons; their implications use monotonicity of real log."""
    return [
        {"name": "delta_gt_2", "left": str(Q(25, 32)), "relation": "<", "right": str(Q(8, 9) ** 2),
         "cleared_left": 2025, "cleared_right": 2048,
         "implies": "delta=log(32/25)/log(9/8)>2; beta>5/8"},
        {"name": "delta_lt_11_over_5", "left": str(Q(25, 32) ** 5), "relation": ">", "right": str(Q(8, 9) ** 11),
         "cleared_left": 25 ** 5 * 9 ** 11, "cleared_right": 32 ** 5 * 8 ** 11,
         "implies": "delta<11/5; beta<3/4"},
        {"name": "kappa_gt_1_over_2", "left": str(Q(25, 18)), "relation": ">", "right": str(Q(9, 8)),
         "cleared_left": 200, "cleared_right": 162,
         "implies": "log(5*sqrt(2)/6)>log(9/8)/2; kappa>1/2"},
        {"name": "small_a_first_power_positive", "left": str(Q(5, 4) ** 3), "relation": ">", "right": str(Q(9, 8) ** 2),
         "cleared_left": 125, "cleared_right": 81,
         "implies": "3*log(5/4)/log(9/8)-2>0"},
        {"name": "small_a_collision_power_positive", "left": str(Q(25, 8)), "relation": ">", "right": str(Q(9, 8)),
         "cleared_left": 25, "cleared_right": 9,
         "implies": "3*log(5/(2*sqrt(2)))/log(9/8)-3/2>0"},
    ]


def build_certificate():
    rows = []
    for epsilon in (-1, 1):
        for t in (1, 2, 3, 5):
            weights = integer_weights(18, t)
            recurrence = divisor_recurrence(weights, epsilon)
            direct = profile_convolution(weights, epsilon)
            require(recurrence == direct, "independent Euler row disagreement")
            require(all(x.denominator == 1 and x >= 0 for x in recurrence), "integer-t semantics failed")
            rows.append({"epsilon": epsilon, "frozen_t": t, "n_max": 18,
                         "coefficients": [str(x) for x in recurrence]})
    frozen_traps = []
    for epsilon in (-1, 1):
        fixed = divisor_recurrence(integer_weights(6, 6), epsilon)[6]
        wrong = wrong_diagonal_recurrence(6, epsilon)[6]
        require(fixed != wrong, "frozen-row negative fixture lost discrimination")
        frozen_traps.append({"epsilon": epsilon, "A_6_6": str(fixed), "wrong_rolling_t_result": str(wrong)})
    polynomial_records = []
    inverse_records = []
    for r in range(3):
        polynomial_records.append({"r": r, **{key: value.encode() for key, value in pure_polynomial_identities(r).items()}})
        inv = inverse_identities(r)
        require(inv["log_model"] == Series(-Q(8, 9) * X ** 4), "formal inverse residual nonzero")
        inverse_records.append({"r": r, "c1": inv["c1"].encode(), "c2": inv["c2"].encode(), "cb": inv["cb"].encode(),
                                "log_s_corrections": {label: inv["minus_L_times_t_correction"].coefficient(*key).encode()
                                                      for label, key in (("u", (1, 0)), ("u^2", (2, 0)), ("v", (0, 1)))},
                                "formal_log_model_nonconstant_residual": []})
    witnesses = rational_witnesses()
    for witness in witnesses:
        lhs, rhs = Q(witness["left"]), Q(witness["right"])
        require(lhs < rhs if witness["relation"] == "<" else lhs > rhs, witness["name"])
    certified_falling_instances = 0
    for m in range(1, 49):
        for ell in range(2 * m + 9):
            depletion = falling_ratio(m, ell)
            require(0 <= depletion <= 1, "depletion outside [0,1]")
            require(0 <= 1 - depletion <= Q(ell * (ell - 1), 2 * m), "depletion union bound failed")
            require(falling_global_bound_check(m, ell), "second-order depletion bound failed")
            certified_falling_instances += 1
    payload = {
        "schema": "report148-exact-finite-certificate-v1",
        "arithmetic": "Python integers and fractions.Fraction; no floating-point conclusions",
        "scope": "Exact identities and finite fixtures only. Not a proof of analytic uniformity, infinite tails, eventual onsets, exact-ratio monotonicity or uniqueness.",
        "euler_rows": rows,
        "frozen_exponent_negative_fixtures": frozen_traps,
        "signed_generalized_binomial_fixture": {"product": "(1+x^2)^(3/2)", "degree": 6, "coefficient": str(factor_coefficients(Q(3, 2), -1, 3)[3]),
            "qualification": "A rational-weight surrogate, not an assertion that one real t produces all surrogate weights."},
        "residue_map": list(RESIDUES), "leading_H_coefficients": [str(h_by_profiles(q)) for q in RESIDUES],
        "normalizer_c": [str(c) for c in NORMALIZERS], "single_5_shifted_map": [(q + 2) % 3 for q in RESIDUES],
        "H_0_through_H_18": [str(h) for h in h_by_recurrence(18)],
        "pure_polynomial_variable": "x=a; w unused", "pure_polynomial_identities": polynomial_records,
        "inverse_variables": "x=s0^(1/3), w=s0^p; quotient ideal (u^3,u*v,v^2)", "inverse_identities": inverse_records,
        "exact_rational_inequality_witnesses": witnesses,
        "global_falling_factorial_finite_check_domain": {"m": "1 through 48", "ell": "0 through 2*m+8", "second_order_constant": 9, "exact_instances_rechecked": certified_falling_instances},
    }
    return {"payload": payload, "payload_sha256": hashlib.sha256(canonical_json(payload).encode("utf-8")).hexdigest()}


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def verify_certificate(path):
    with open(path, encoding="utf-8") as stream:
        saved = json.load(stream)
    require(saved == build_certificate(), "certificate content or digest differs from exact regeneration")
    return saved["payload_sha256"]


def write_certificate_exclusive(path, certificate):
    """Create a new certificate, without overwriting or following any symlink.

    POSIX directory-descriptor traversal keeps every component protected by
    O_NOFOLLOW, including if a directory is renamed during traversal.  The
    final O_EXCL creation rejects existing regular files and dangling symlinks.
    """
    require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"),
            "safe certificate creation requires POSIX O_NOFOLLOW/O_DIRECTORY")
    output = Path(path).absolute()
    require(output.name not in ("", ".", "..") and ".." not in output.parts,
            "output must have a filename and must not contain '..' components")
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    directory_fd = os.open(output.anchor, directory_flags)
    try:
        for component in output.parts[1:-1]:
            next_fd = os.open(component, directory_flags, dir_fd=directory_fd)
            os.close(directory_fd)
            directory_fd = next_fd
        file_fd = os.open(output.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                          0o644, dir_fd=directory_fd)
        with os.fdopen(file_fd, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    finally:
        os.close(directory_fd)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write-certificate", type=Path)
    group.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.write_certificate:
        certificate = build_certificate()
        try:
            write_certificate_exclusive(args.write_certificate, certificate)
        except (OSError, ValueError) as error:
            parser.exit(2, "Certificate output refused: " + str(error) + "\n")
        print("Wrote deterministic certificate:", args.write_certificate)
        print("Payload SHA-256:", certificate["payload_sha256"])
    else:
        print("Exact certificate verified; payload SHA-256:", verify_certificate(args.verify))


if __name__ == "__main__":
    main()
