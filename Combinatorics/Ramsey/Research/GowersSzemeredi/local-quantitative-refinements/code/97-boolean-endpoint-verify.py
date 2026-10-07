#!/usr/bin/env python3
"""Exact regression checks for Boolean endpoint rigidity.

Standard library only. Finite checks supplement, and do not replace, the proofs.
No assertion is used as a proof check, so `python -O` performs the same tests.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import random
from fractions import Fraction
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def bit(x: int, mask: int) -> int:
    return (x & mask).bit_count() & 1


def canonical(hs: tuple[int, ...]) -> int:
    """C_d with u=x_1 and v=x_2; handles zero and inactive directions."""
    zeros = [h for h in hs if (h & 1) == 0]
    if len(zeros) >= 2:
        return 0
    if zeros:
        return (zeros[0] >> 1) & 1
    return sum((h >> 1) & 1 for h in hs) & 1


def canonical_direct(hs: tuple[int, ...]) -> int:
    return sum(((h >> 1) & 1) * math.prod(k & 1 for j, k in enumerate(hs) if j != i)
               for i, h in enumerate(hs)) & 1


def mobius(values: list[int], modulus: int) -> list[int]:
    c = values.copy()
    n = (len(c) - 1).bit_length()
    require(len(c) == 1 << n, "truth table must have power-of-two length")
    for j in range(n):
        for mask in range(len(c)):
            if mask & (1 << j):
                c[mask] = (c[mask] - c[mask ^ (1 << j)]) % modulus
    return c


def values_from_coefficients(c: list[int], modulus: int) -> list[int]:
    values = c.copy()
    n = (len(c) - 1).bit_length()
    for j in range(n):
        for mask in range(len(c)):
            if mask & (1 << j):
                values[mask] = (values[mask] + values[mask ^ (1 << j)]) % modulus
    return values


def allowed_coefficient(a: int, size: int, degree: int, modulus: int) -> bool:
    return a % modulus == 0 if size > degree else (a * 2 ** (degree-size+1)) % modulus == 0


def polynomial_certificate(values: list[int], degree: int, modulus: int) -> bool:
    return all(allowed_coefficient(a, mask.bit_count(), degree, modulus)
               for mask, a in enumerate(mobius(values, modulus)) if mask)


def literal_degree_test(values: list[int], degree: int, modulus: int) -> bool:
    """All iterated differences, deduplicated as exact function tables."""
    states = {tuple(a % modulus for a in values)}
    zero = (0,) * len(values)
    for _ in range(degree + 1):
        states = {tuple((v[x ^ h] - v[x]) % modulus for x in range(len(v)))
                  for v in states for h in range(len(v))}
        if states == {zero}:
            return True
    return states == {zero}


def endpoint_certificate(values: list[int], d: int, modulus: int) -> bool:
    return all(allowed_coefficient(a, mask.bit_count(), d-1, modulus)
               for mask, a in enumerate(mobius(values, modulus)) if mask not in (0, 1))


def relative_certificate(values: list[int], d: int, modulus: int) -> bool:
    return all(allowed_coefficient(a, mask.bit_count(), d-1, modulus)
               for mask, a in enumerate(mobius(values, modulus)) if mask & ~3)


def four_point_coefficients(d: int) -> dict[tuple[int, ...], int]:
    result: dict[tuple[int, ...], int] = {}
    for hs in itertools.product(range(4), repeat=d):
        active = tuple(mask for mask in (1, 2, 3) if all(bit(h, mask) for h in hs))
        sign = 1 - 2 * canonical(hs)
        result[active] = result.get(active, 0) + sign
    return {key: value for key, value in result.items() if value}


def expected_four_point_coefficients(d: int) -> dict[tuple[int, ...], int]:
    s, m = (-1) ** d, 2 ** d - 2*d - 2
    result = {(): 4**d - (d+3)*2**d + 4*d + 3, (1,): -(1+s),
              (2,): m, (3,): m, (1,3): 1, (2,3): 1, (1,2): s}
    return {key: value for key, value in result.items() if value}


def phase_cube_histogram(values: list[int], d: int, modulus: int) -> list[int]:
    n = len(values)
    hist = [0] * modulus
    for hs in itertools.product(range(n), repeat=d):
        v = values.copy()
        for h in hs:
            v = [(v[x ^ h] - v[x]) % modulus for x in range(n)]
        sign = 1 - 2 * canonical(hs)
        for a in v:
            hist[a] += sign
    return hist


def reduce_power_two(hist: list[int]) -> list[int]:
    half = len(hist) // 2
    return [hist[i] - hist[i + half] for i in range(half)]


def reduce_three_times_power_two(hist: list[int]) -> list[int]:
    """Reduce modulo Phi_(3*2^a)=X^(2^a)-X^(2^(a-1))+1, a>=1."""
    degree = len(hist) // 3
    require(degree >= 2 and degree & (degree-1) == 0, "invalid cyclotomic order")
    p = hist.copy()
    for k in range(len(p)-1, degree-1, -1):
        a = p[k]
        p[k] = 0
        p[k-degree//2] += a
        p[k-degree] -= a
    return p[:degree]


def four_point_prediction_histogram(values: list[int], d: int, modulus: int) -> list[int]:
    """4 times the claimed numerator, expressed in Z[zeta_modulus]."""
    a = 2**(d-2) * (values[0]-values[1]+values[2]-values[3])
    b = 2**(d-2) * (values[0]+values[1]-values[2]-values[3])
    c = 2**(d-2) * (values[0]-values[1]-values[2]+values[3])
    s, m = (-1)**d, 2**d-2*d-2
    hist = [0]*modulus
    hist[0] = 4*(4**d-(d+3)*2**d+4*d+3)
    for exponent, coefficient in ((a, -2*(1+s)), (b, 2*m), (c, 2*m)):
        for sign in (-1, 1):
            hist[(sign*exponent) % modulus] += coefficient
    for x, y, coefficient in ((a,c,1), (b,c,1), (a,b,s)):
        for sx, sy in itertools.product((-1,1), repeat=2):
            hist[(sx*x+sy*y) % modulus] += coefficient
    return hist


def hessian_census(n: int, d: int) -> list[tuple[Fraction, Fraction]]:
    size = 1 << n
    acc = [[0,0] for _ in range(size)]
    for hs in itertools.product(range(size), repeat=d):
        sign = 1 - 2*canonical(hs)
        au = int(all(h & 1 for h in hs))
        for xi in range(1,size):
            if all(bit(h,xi) for h in hs):
                acc[xi][au] += sign
    scale = Fraction(4**d, size**d)
    return [(scale*a, scale*b) for a,b in acc]


def gaussian_mul(a: tuple[int,int], b: tuple[int,int]) -> tuple[int,int]:
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def gaussian_energy(values: list[tuple[int,int]], denominator: int, d: int) -> Fraction:
    size = len(values)
    numerator = 0
    for hs in itertools.product(range(size), repeat=d-1):
        v = values.copy()
        for h in hs:
            v = [gaussian_mul(v[x ^ h], (v[x][0], -v[x][1])) for x in range(size)]
        real = imag = 0
        for x, (a,b) in enumerate(v):
            sign = 1 - 2*canonical(hs+(x,))
            real += sign*a
            imag += sign*b
        numerator += real*real + imag*imag
    return Fraction(numerator, size**(d+1)*denominator**(2**d))


def main() -> dict:
    rng = random.Random(20261007)
    result: dict = {"status": "passed", "arithmetic": "integer, rational, and exact cyclotomic",
                    "proof_assistant_verification": False}
    # Independent multilinear and zero-pattern formulas.
    for d in range(3,10):
        for _ in range(80):
            hs = tuple(rng.randrange(32) for _ in range(d))
            require(canonical(hs) == canonical_direct(hs), "tensor convention")
    result["tensor_convention_checks"] = 560
    ledger = []
    for d in range(3,10):
        require(four_point_coefficients(d) == expected_four_point_coefficients(d),
                f"four-point coefficients d={d}")
        m = 2**d-2*d-2
        # Multiaffine maximization is exact at the eight vertices.
        values = []
        for X,Y,Z in itertools.product((-1,1), repeat=3):
            s = (-1)**d
            A = 4**d-(d+3)*2**d+4*d+3
            values.append(Fraction(A-(1+s)*X+m*(Y+Z)+X*Z+Y*Z+s*X*Y,4**d))
        b = 1-Fraction(d+1,2**d)
        require(max(values) == b, f"vertex maximum d={d}")
        ledger.append({"degree": d, "endpoint": str(b), "normal_gap": m,
                       "sharp_leading_distance_coefficient": str(Fraction(2,m)) if m else None,
                       "direction_tuples": 4**d})
    result["four_point_ledger"] = ledger
    result["four_point_direction_tuples"] = sum(4**d for d in range(3,10))
    phase_checks = 0
    for d in range(3,7):
        M = 2**(d+3)
        for _ in range(8):
            values = [rng.randrange(M) for _ in range(4)]
            actual = reduce_power_two(phase_cube_histogram(values,d,M))
            expected = reduce_power_two(four_point_prediction_histogram(values,d,M))
            require(actual == expected, f"cyclotomic identity d={d}")
            phase_checks += 1
    result["cyclotomic_four_point_identities"] = phase_checks
    spectral = []
    for n,d in ((3,3),(3,4),(3,5),(4,4)):
        actual = hessian_census(n,d)
        for xi, pair in enumerate(actual):
            if xi in (0,1): expected = (Fraction(0), Fraction(0))
            elif xi == 2: expected = (Fraction(2**d-2*d-1), Fraction((-1)**d))
            elif xi == 3: expected = (Fraction(2**d-2*d-1), Fraction(1))
            else: expected = (Fraction(2**d-d-1), Fraction(0))
            require(pair == expected, f"Hessian n={n}, d={d}, xi={xi}")
        spectral.append({"dimension": n, "degree": d, "frequencies": 1<<n})
    result["hessian_symbolic_X_censuses"] = spectral
    literal = 0
    for n in (1,2,3):
        for M in (4,8):
            for k in (2,3,4):
                for _ in range(4):
                    values = [rng.randrange(M) for _ in range(1<<n)]
                    require(values_from_coefficients(mobius(values,M),M) == values,
                            "Mobius inversion")
                    require(polynomial_certificate(values,k,M) == literal_degree_test(values,k,M),
                            f"literal degree test n={n}, k={k}, M={M}")
                    literal += 1
    result["literal_all_direction_polynomial_checks"] = literal
    good = 0
    # Exhaustive normalized fourth-root phase tables on F_2^3.
    for tail in itertools.product(range(4),repeat=7):
        values = [0]+list(tail)
        derivative = [(values[x ^ 4]-values[x]) % 4 for x in range(8)]
        relative = polynomial_certificate(derivative,2,4)
        require(relative == relative_certificate(values,4,4), "relative gluing census")
        require(relative == endpoint_certificate(values,4,4), "endpoint phase census")
        good += int(relative)
    require(good == 8192, "fourth-root endpoint count")
    result["normalized_fourth_root_tables"] = {"dimension": 3, "degree": 4,
                                                 "tested": 16384, "endpoint_certificates": good}
    endpoint_cases = 0
    for d in (4,5):
        M = 3*2**(d-1)
        for _ in range(3):
            c = [rng.randrange(M)]+[0]*7
            for mask in range(1,8):
                size = mask.bit_count()
                if size <= d-1:
                    order = 2**(d-size)
                    c[mask] = rng.randrange(order)*(M//order)
            c[1] = (c[1]+M//3) % M  # a genuinely non-dyadic endpoint parameter
            values = values_from_coefficients(c,M)
            require(endpoint_certificate(values,d,M), "constructed endpoint certificate")
            reduced = reduce_three_times_power_two(phase_cube_histogram(values,d,M))
            target = 8**(d+1)*(1-Fraction(d+1,2**d))
            require(target.denominator == 1, "normalization")
            require(reduced == [target.numerator]+[0]*(len(reduced)-1), "endpoint cube energy")
            endpoint_cases += 1
    result["inactive_coordinate_non_dyadic_endpoint_checks"] = endpoint_cases
    # A non-endpoint and its degree-five gauge counterpart.
    values = [int((x & 7) == 7) for x in range(8)]
    hist = phase_cube_histogram(values,4,4)
    bad_energy = Fraction(hist[0]-hist[2],8**5)
    require(bad_energy == Fraction(101,256), "quartic non-endpoint regression")
    require(not endpoint_certificate(values,4,4), "quartic non-endpoint certificate")
    require(endpoint_certificate(values,5,4), "quintic gauge certificate")
    result["quartic_triple_monomial_over_four_energy"] = str(bad_energy)
    # Arbitrary bounded complex inputs, including zeros and non-unit amplitudes.
    alphabet = [(0,0),(5,0),(0,5),(-5,0),(0,-5),(3,4),(3,0),(1,2)]
    bounded = 0
    for size,d,count in ((4,3,8),(4,4,8),(4,5,4),(8,4,4)):
        for _ in range(count):
            values = [rng.choice(alphabet) for _ in range(size)]
            energy = gaussian_energy(values,5,d)
            b = 1-Fraction(d+1,2**d)
            require(0 <= energy <= b, "bounded complex energy cap")
            if d >= 4:
                mass = Fraction(sum(a*a+c*c for a,c in values),25*size)
                require(b-energy >= (1-mass)/4, "amplitude deficit")
            bounded += 1
    result["gaussian_rational_bounded_function_checks"] = bounded
    # Exact constants, comparison inequalities and component counts.
    constants = []
    for d in range(4,21):
        m = 2**d-2*d-2
        ell = m-1 if d % 2 == 0 else m
        require(m >= 6 and ell > 0, "positive transverse gap")
        for p,q,X in itertools.product((Fraction(0),Fraction(1,2),Fraction(1),Fraction(2)),
                                        (Fraction(0),Fraction(1,2),Fraction(1),Fraction(2)),
                                        (Fraction(-1),Fraction(0),Fraction(1))):
            D = (m+1+(-1)**d*X)*p+(m+1+X)*q-p*q
            require(D >= ell*(p+q), "quotient coercivity")
        components_n2 = 2**(sum((d-j)*math.comb(2,j) for j in range(1,min(d-1,2)+1))-(d-1))
        constants.append({"degree": d, "m": m, "ell": ell,
                          "components_dimension_two": components_n2})
    result["constant_ledger"] = constants
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    record = main()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(record,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps(record,indent=2,sort_keys=True))
