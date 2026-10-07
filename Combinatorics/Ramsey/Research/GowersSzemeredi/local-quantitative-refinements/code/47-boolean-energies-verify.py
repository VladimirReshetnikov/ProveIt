#!/usr/bin/env python3
"""Exact finite checks for Boolean obstruction energies.

Python standard library only. No network access, floating point arithmetic,
external files, proof-assistant claims, or assertion-dependent checks.
Run from any directory; results are written relative to this package.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json
from pathlib import Path
import random
import sys
from typing import Callable, Iterable, Sequence

Gaussian = tuple[int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def mul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def conj(a: Gaussian) -> Gaussian:
    return (a[0], -a[1])


def derivative(values: Sequence[Gaussian], h: int) -> list[Gaussian]:
    return [mul(values[x ^ h], conj(values[x])) for x in range(len(values))]


def dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def canonical_frequency(hs: Sequence[int]) -> int:
    """Frequency of C_d(hs, x), with u=x_0 and v=x_1."""
    zeros = [h for h in hs if not (h & 1)]
    if len(zeros) >= 2:
        return 0
    if len(zeros) == 1:
        return (zeros[0] >> 1) & 1
    return 2 | (sum((h >> 1) & 1 for h in hs) & 1)


def pure_frequency(hs: Sequence[int]) -> int:
    return int(all(h & 1 for h in hs))


def energy(values: Sequence[Gaussian], denominator: int, degree: int,
           frequency: Callable[[Sequence[int]], int]) -> Fraction:
    """Exact selected energy for values[x]/denominator in Q(i)."""
    n = len(values)
    require(n > 0 and n & (n-1) == 0, "Group size must be a positive power of two")
    require(degree >= 2 and denominator > 0, "Invalid degree or denominator")
    total = 0
    for hs in product(range(n), repeat=degree-1):
        g = list(values)
        for h in hs:
            g = derivative(g, h)
        xi = frequency(hs)
        re = sum((-1 if dot(xi, x) else 1)*g[x][0] for x in range(n))
        im = sum((-1 if dot(xi, x) else 1)*g[x][1] for x in range(n))
        total += re*re + im*im
    return Fraction(total, n**(degree+1) * denominator**(2**degree))


def cube_energy(values: Sequence[Gaussian], denominator: int, degree: int,
                frequency: Callable[[Sequence[int]], int]) -> Fraction:
    """Independent full-cube computation, used only on the smallest groups."""
    n = len(values)
    re = im = 0
    for hs in product(range(n), repeat=degree):
        g = list(values)
        for h in hs:
            g = derivative(g, h)
        sign = -1 if dot(frequency(hs[:-1]), hs[-1]) else 1
        re += sign * sum(t[0] for t in g)
        im += sign * sum(t[1] for t in g)
    require(im == 0, "Full selected cube average is not real")
    return Fraction(re, n**(degree+1) * denominator**(2**degree))


def formal_derivative_monomial(n: int, hs: Sequence[int], x: int) -> tuple[tuple[int, int], ...]:
    """Exponents of f(y) and conjugate(f(y)), not values of a test function."""
    out = [[0, 0] for _ in range(n)]
    r = len(hs)
    for eps in product((0, 1), repeat=r):
        y = x
        for bit, h in zip(eps, hs):
            if bit:
                y ^= h
        parity = (r - sum(eps)) & 1
        out[y][parity] += 1
    return tuple(tuple(pair) for pair in out)


def verify_periods() -> dict:
    cases = 0
    forbidden_pairs = 0
    for n, max_r in ((2, 5), (4, 4), (8, 3)):
        for r in range(1, max_r+1):
            for hs in product(range(n), repeat=r):
                for x in range(n):
                    mon = formal_derivative_monomial(n, hs, x)
                    conjugate_mon = tuple((b, a) for a, b in mon)
                    for h in hs:
                        require(formal_derivative_monomial(n, hs, x ^ h) == conjugate_mon,
                                "Individual-direction conjugation identity failed")
                        cases += 1
                    for h in hs[1:]:
                        require(formal_derivative_monomial(n, hs, x ^ hs[0] ^ h) == mon,
                                "Even-span period identity failed")
                        cases += 1
    # Formal pairing of summands at a forced forbidden frequency.
    for n in (4, 8):
        for z in range(n):
            if z & 1:
                continue
            for h in range(n):
                if not h & 1:
                    continue
                w = h ^ z
                for x in range(n):
                    require(formal_derivative_monomial(n, (h, z), x) ==
                            formal_derivative_monomial(n, (h, z), x ^ w),
                            "Forbidden-frequency monomials do not match")
                    require(dot(1, x) != dot(1, x ^ w), "Forbidden-frequency signs do not cancel")
                    forbidden_pairs += 1
    return {"identity_comparisons": cases, "exact_forbidden_pair_comparisons": forbidden_pairs,
            "method": "formal unconjugated/conjugated exponent pairs; valid at zeros"}


def canonical_constant(degree: int) -> Fraction:
    good = sum(canonical_frequency(hs) == 0 for hs in product(range(4), repeat=degree-1))
    return Fraction(good, 4**(degree-1))


def verify_canonical(max_degree: int) -> dict:
    counts = []
    for d in range(3, max_degree+1):
        actual = canonical_constant(d)
        target = 1 - Fraction(d+1, 2**d)
        require(actual == target, f"Constant canonical count failed at degree {d}")
        counts.append({"degree": d, "zero_frequencies": actual.numerator,
                       "reduced_denominator": actual.denominator,
                       "energy": str(actual), "raw_direction_tuples": 4**(d-1)})
    previous = Fraction(1, 2)
    for d in range(4, 1001):
        value = Fraction(1, 4) + Fraction(1, 4)*(1-Fraction(1, 2**(d-2))) + previous/2
        require(value == 1-Fraction(d+1, 2**d), f"Induction recurrence failed at {d}")
        previous = value
    return {"counts": counts, "rational_recurrence_verified_through_degree": 1000}


def trilinear_outputs(coeff: Sequence[int]) -> list[int]:
    A, B, C, D = coeff
    return [A, D, A ^ B ^ C ^ D, B, C, A ^ B, A ^ C, C ^ D, B ^ D, B ^ C]


def weight3(coeff: Sequence[int]) -> int:
    weights = (1, 1, 1, 3, 3, 3, 3, 3, 3, 6)
    return sum(w for w, value in zip(weights, trilinear_outputs(coeff)) if value != 0)


def pure3(coeff: Sequence[int]) -> bool:
    A, B, C, D = coeff
    return (A != 0 and B == C == D == 0) or (D != 0 and A == B == C == 0) or (A == B == C == D != 0)


def scalar_tensor_bitset(n: int, degree: int, basis_tuple: Sequence[int]) -> int:
    """Truth-table bitset of one symmetric basis coefficient on (F_2^n)^degree."""
    size = 1 << n
    ans = 0
    index = 0
    target = tuple(basis_tuple)
    for hs in product(range(size), repeat=degree):
        parity = 0
        for inds in product(range(n), repeat=degree):
            if tuple(sorted(inds)) != target:
                continue
            val = 1
            for h, i in zip(hs, inds):
                val &= (h >> i) & 1
            parity ^= val
        ans |= parity << index
        index += 1
    return ans


def verify_support() -> dict:
    scalar_rows = []
    hist = Counter()
    for coeff in product(range(2), repeat=4):
        w = weight3(coeff)
        hist[w] += 1
        if any(coeff) and not pure3(coeff):
            require(w >= 14, "Scalar binary trilinear support bound failed")
        scalar_rows.append({"coefficients_ABCD": ''.join(map(str, coeff)), "weight_out_of_64": w,
                            "pure": pure3(coeff)})
    vector_hist = Counter()
    for coeff in product(range(4), repeat=4):
        w = weight3(coeff)
        vector_hist[w] += 1
        if any(coeff) and not pure3(coeff):
            require(w >= 14, "Vector-valued binary trilinear support bound failed")
    # Independent evaluation of all scalar symmetric trilinear tensors on F_2^3.
    n = 3
    basis = list(combinations_with_replacement(range(n), 3))
    bitsets = [scalar_tensor_bitset(n, 3, I) for I in basis]
    pure_masks = set()
    for u in range(1, 1 << n):
        mask = 0
        for j, I in enumerate(basis):
            if all((u >> i) & 1 for i in I):
                mask |= 1 << j
        pure_masks.add(mask)
    hist3 = Counter()
    minimum = 512
    for mask in range(1 << len(basis)):
        bits = 0
        for j, table in enumerate(bitsets):
            if (mask >> j) & 1:
                bits ^= table
        w = bits.bit_count()
        hist3[w] += 1
        if mask and mask not in pure_masks:
            require(w >= 112, "Three-dimensional non-pure support bound failed")
            minimum = min(minimum, w)
    require(minimum == 112, "The sharp three-dimensional example was not found")
    return {"binary_scalar_rows": scalar_rows, "binary_scalar_histogram": dict(sorted(hist.items())),
            "binary_vector_F2_squared_cases": 256,
            "binary_vector_histogram": dict(sorted(vector_hist.items())),
            "three_dimensional_scalar_cases": 1024,
            "three_dimensional_scalar_minimum_nonpure": "112/512 = 7/32",
            "three_dimensional_histogram": dict(sorted(hist3.items()))}


def binary_coeff_frequency(coeff: int, hs: Sequence[int]) -> int:
    poly = 1
    for h in hs:
        poly = (poly if h & 1 else 0) ^ ((poly << 1) if h & 2 else 0)
    a = (coeff & poly).bit_count() & 1
    b = (coeff & (poly << 1)).bit_count() & 1
    return a | (b << 1)


def verify_small_tensors() -> dict:
    out = []
    for d in range(3, 7):
        count = 0
        maximum = Fraction(0)
        maximizers = []
        for coeff in range(1 << (d+1)):
            middle = [(coeff >> j) & 1 for j in range(1, d)]
            integrable = len(set(middle)) == 1
            if integrable:
                continue
            count += 1
            val = Fraction(sum(binary_coeff_frequency(coeff, hs) == 0
                               for hs in product(range(4), repeat=d-1)), 4**(d-1))
            require(val <= 1-Fraction(d+1, 2**d), "Small-tensor constant test exceeded theorem")
            if val > maximum:
                maximum, maximizers = val, [coeff]
            elif val == maximum:
                maximizers.append(coeff)
        require(maximum == 1-Fraction(d+1, 2**d), "Sharp small-tensor constant not attained")
        out.append({"degree": d, "nonintegrable_binary_tensors": count,
                    "constant_function_maximum": str(maximum), "maximizing_coefficient_masks": maximizers})
    return {"results": out, "scope": "All binary tensors, but only the constant test function; not an optimization proof."}


def verify_exact_energies() -> dict:
    rng = random.Random(20261006)
    cases = []
    slicing = []
    cube_checks = 0
    pool = [(2, 0), (-2, 0), (0, 2), (0, -2), (1, 1), (1, 0), (0, 0)]
    for n, d in ((2,3), (2,4), (2,5), (2,6), (3,3), (3,4), (3,5), (4,3), (4,4)):
        values = [rng.choice(pool) for _ in range(1 << n)]
        actual = energy(values, 2, d, canonical_frequency)
        bound = 1 - Fraction(d+1, 2**d)
        require(0 <= actual <= bound, "Exact Gaussian-rational canonical energy exceeds theorem")
        cases.append({"dimension": n, "degree": d, "input_numerators": values,
                      "input_denominator": 2, "energy": str(actual), "bound": str(bound)})
        if n == 2 and d <= 4:
            cube = cube_energy(values, 2, d, canonical_frequency)
            require(actual == cube, "Selected energy and independent full-cube energy disagree")
            cube_checks += 1
        if n == 2 and d >= 4:
            slice_value = Fraction(0)
            caps = Fraction(0)
            for z in range(1 << n):
                g = derivative(values, z)
                def freq(hs: Sequence[int], z: int = z) -> int:
                    return (canonical_frequency(hs) if z & 1 else 0) ^ ((z >> 1 & 1)*pure_frequency(hs))
                piece = energy(g, 4, d-1, freq)
                if z & 1:
                    cap = 1-Fraction(d, 2**(d-1))
                elif z & 2:
                    cap = 1-Fraction(1, 2**(d-2))
                else:
                    cap = Fraction(1)
                require(piece <= cap, "A quarter-slice bound failed")
                slice_value += piece/Fraction(1 << n)
                caps += cap/Fraction(1 << n)
            require(slice_value == actual, "Exact derivative slicing failed")
            require(caps == bound, "Slice caps do not sum to canonical bound")
            slicing.append({"degree": d, "exact_slice_identity": True, "exact_cap_sum": str(caps)})
    fixed = []
    for n in (2, 3):
        values = [rng.choice(pool) for _ in range(1 << n)]
        for m in (2, 3, 4):
            for z in range(1 << n):
                if z & 1:
                    continue
                val = energy(derivative(values, z), 4, m, pure_frequency)
                cap = 1-Fraction(1, 2**(m-1))
                require(val <= cap, "Fixed-derivative rank-one bound failed")
                fixed.append({"dimension": n, "degree": m, "shift": z, "energy": str(val), "cap": str(cap)})
    return {"canonical_tests": cases, "fixed_derivative_tests": fixed,
            "exact_slicing_checks": slicing, "independent_full_cube_checks": cube_checks,
            "arithmetic": "Exact Gaussian integer products and fractions; no floating point"}



def additive_derivative(values: Sequence[int], h: int, modulus: int) -> list[int]:
    return [(values[x ^ h]-values[x]) % modulus for x in range(len(values))]


def support_tensor_value(support: int, hs: Sequence[int]) -> int:
    """T_A = sum_{J subset A} (sum_{i in J} x_i)^{tensor d}, over F_2."""
    answer = 0
    subset = support
    while True:
        answer ^= int(all(dot(subset, h) for h in hs))
        if subset == 0:
            break
        subset = (subset-1) & support
    return answer


def verify_primitives() -> dict:
    rng = random.Random(20261007)
    top_checks = 0
    degree_checks = 0
    for n in range(1, 5):
        size = 1 << n
        for d in range(2, 9):
            modulus = 1 << d
            for support in range(1, size):
                a = support.bit_count()
                if a > d:
                    continue
                # P_A = (2^(a-1) product_{i in A} x_i) / 2^d modulo 1.
                values = [(1 << (a-1)) if x & support == support else 0
                          for x in range(size)]
                directions: Iterable[tuple[int, ...]]
                if n <= 2 and d <= 5:
                    directions = product(range(size), repeat=d)
                else:
                    directions = [tuple(rng.randrange(size) for _ in range(d))
                                  for _ in range(24)]
                for hs in directions:
                    g = values
                    for h in hs:
                        g = additive_derivative(g, h, modulus)
                    expected = (modulus//2) * support_tensor_value(support, hs)
                    require(all(v == expected for v in g), "Explicit primitive top derivative failed")
                    top_checks += 1
                for _ in range(24):
                    g = values
                    for _ in range(d+1):
                        g = additive_derivative(g, rng.randrange(size), modulus)
                    require(all(v == 0 for v in g), "Explicit primitive degree bound failed")
                    degree_checks += 1
    return {"top_derivative_checks": top_checks, "degree_bound_checks": degree_checks,
            "dimensions": [1, 2, 3, 4], "degrees": list(range(2, 9)),
            "arithmetic": "Integer differences modulo 2^d",
            "scope": "Exhaustive directions when n<=2 and d<=5; seeded exact samples otherwise"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-degree', type=int, default=10,
                        help='Largest degree for exhaustive two-coordinate constant counts (3..11)')
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    if not 3 <= args.max_degree <= 11:
        parser.error('--max-degree must be between 3 and 11')
    report = {"status": "passed", "arithmetic": "exact", "seed": 20261006,
              "periods": verify_periods(), "primitives": verify_primitives(),
              "canonical": verify_canonical(args.max_degree),
              "multilinear_support": verify_support(), "small_tensors": verify_small_tensors(),
              "energies": verify_exact_energies(),
              "limitations": ["Finite checks supplement the proofs; they do not establish all dimensions.",
                              "No proof assistant was run.",
                              "No external literature-priority certification is claimed."]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(f'PASS: exact checks written to {args.output}')
    print(f'Formal period comparisons: {report["periods"]["identity_comparisons"]}')
    print('Sharp symmetric energies, degrees 3..6: 1/2, 11/16, 13/16, 57/64')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, RuntimeError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
