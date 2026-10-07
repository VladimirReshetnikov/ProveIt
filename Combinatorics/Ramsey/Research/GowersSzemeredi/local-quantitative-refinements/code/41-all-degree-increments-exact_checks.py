#!/usr/bin/env python3
"""Bounded exact diagnostics for Report 277, not mathematical proofs.

All arithmetic is integer or Fraction arithmetic. Recurrence and partition
bounds are represented by their exponents: this program never constructs the
astronomical theorem-scale T, H, R or partitions. Finite rational recurrence
samples do not certify recurrence for real coefficients. Finite checks of the
all-k induction's algebra supplement, and never replace, the written induction.

The CLI emits deterministic sorted JSON, including with Python -O, -I, -B and
-X int_max_str_digits=640. Every public numerical interface validates bounded
inputs with runtime exceptions, not assertions. No third-party modules needed.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import comb, factorial, gcd
import re
import sys

Q = Fraction
MAX_K = 32
MAX_NMAX = 8
MAX_MODULUS = 64
MAX_DENOMINATOR = 512
MAX_LENGTH = 4096
MAX_POLY_DEGREE = 8
MAX_COEFFICIENT = 2**128 - 1
MAX_RATIO = 2**1024 - 1
MAX_SYMBOLIC_EXPONENT = 2**1024 - 1
MAX_R = 4096
DIGIT_CAP = 64
PI_UPPER = Q(22, 7)  # Uses the analytic fact pi < 22/7, not a computed proof.


class CheckFailure(RuntimeError):
    """A failed diagnostic, also active with optimization enabled."""


def _ensure(condition, message):
    if not condition:
        raise CheckFailure(message)


def _integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in [{low}, {high}]")
    return value


def _boolean(value, name):
    if type(value) is not bool:
        raise ValueError(f"{name} must be boolean")
    return value


def _fraction(value, name):
    if type(value) not in (int, Q):
        raise ValueError(f"{name} must be an integer or Fraction")
    value = Q(value)
    _integer(value.numerator, name + " numerator", -MAX_COEFFICIENT, MAX_COEFFICIENT)
    _integer(value.denominator, name + " denominator", 1, MAX_COEFFICIENT)
    return value


def _coefficients(values):
    if type(values) not in (tuple, list) or not 1 <= len(values) <= MAX_POLY_DEGREE + 1:
        raise ValueError("coefficients must be a list or tuple of length 1..9")
    return tuple(_fraction(v, "coefficient") for v in values)


def _subset(n, values):
    if type(values) not in (set, frozenset, tuple, list) or len(values) > n:
        raise ValueError("subset must be a bounded collection, not an iterator")
    for v in values:
        _integer(v, "residue", 0, n - 1)
    if len(set(values)) != len(values):
        raise ValueError("subset contains duplicate residues")
    return frozenset(values)


def _parse(value, name, low, high):
    if type(value) is not str or not 1 <= len(value) <= DIGIT_CAP:
        raise ValueError(f"{name} accepts at most 64 ASCII decimal digits")
    if re.fullmatch(r"[0-9]+", value) is None:
        raise ValueError(f"{name} requires an ASCII decimal integer")
    canonical = value.lstrip("0") or "0"
    if len(canonical) > len(str(high)):
        raise ValueError(f"{name} exceeds its diagnostic cap")
    return _integer(int(canonical), name, low, high)


def _jsonable(value):
    if type(value) is Q:
        return str(value)
    if isinstance(value, dict):
        return {key: _jsonable(child) for key, child in value.items()}
    if isinstance(value, (tuple, list)):
        return [_jsonable(child) for child in value]
    return value


def _leq_times_pow2(left, right, exponent):
    """Compare bounded integers without materializing a huge power of two."""
    if left <= right or exponent >= left.bit_length():
        return True
    return left <= (right << exponent)


def _centered(value):
    residue = value % 1
    return residue - 1 if residue > Q(1, 2) else residue


def recurrence_parameters(k, sharper_cubic=False):
    """Return formal p <= 2**A * R**B exponents for 2 <= k <= 32.

    sharper_cubic is allowed only at degree three. This describes the proven
    candidate's unconditional bound, never the conditional p < T/R**2 bound.
    """
    _integer(k, "degree", 2, MAX_K)
    _boolean(sharper_cubic, "sharper_cubic")
    if sharper_cubic and k != 3:
        raise ValueError("the separately optimized recurrence is cubic only")
    r = k - 1
    D = 2**r
    divisor_c = 3*r**(2*r + 2)
    A = 128 if sharper_cubic else 16*(D + divisor_c + k*k)
    return {"k": k, "r": r, "D": D, "divisor_c": divisor_c,
            "A": A, "B": 2**k + 8, "sharper_cubic": sharper_cubic}


def source_constant(k):
    """Return K_k exactly for bounded k; this is not a partition size."""
    _integer(k, "degree", 1, MAX_K)
    return factorial(k)**2 * 2**((k + 1)**2)


def density_exponent(k):
    """Return D_1=4 and D_k=K_k/4+1, with an exact source comparison."""
    _integer(k, "degree", 1, MAX_K)
    K = source_constant(k)
    D = 4 if k == 1 else K//4 + 1
    _ensure(D <= K, "density exponent implies pinned source exponent")
    return D


def partition_budget(k, sharper_cubic=False):
    """Return (c,e) for n >= 2**c * L**e, without constructing this size."""
    _integer(k, "degree", 1, MAX_K)
    _boolean(sharper_cubic, "sharper_cubic")
    if sharper_cubic and k != 3:
        raise ValueError("the separate sharper budget is cubic only")
    if k == 1:
        return {"k": 1, "c": 6, "e": 3, "sharper_cubic": False}
    c, e = 116, 38
    for degree in range(3, k + 1):
        p = recurrence_parameters(degree, sharper_cubic and degree == 3)
        B, A = p["B"], p["A"]
        m = degree*B + 1
        c, e = A + (degree + 7)*B + m*(c + e), B + m*e
    return {"k": k, "c": c, "e": e, "sharper_cubic": sharper_cubic}


def budget_diagnostic(k):
    """Check finite exact algebra underlying the written uniform induction."""
    _integer(k, "degree", 2, MAX_K)
    b = partition_budget(k)
    K = source_constant(k)
    _ensure(4*(b["c"] + b["e"]) <= K, "U_k <= K_k/4")
    p = recurrence_parameters(k)
    r, D, A, B, c0 = (p[key] for key in ("r", "D", "A", "B", "divisor_c"))
    _ensure(A >= 64 and B + 1 <= A and 2*r <= A, "recurrence size preliminaries")
    _ensure(A >= k*k + 2*D, "first Weyl term exponent budget")
    _ensure(r*(A + B + 1) <= A*A, "third Weyl term polynomial prefactor")
    _ensure(_leq_times_pow2(A*A, 1, A//4), "A squared <= 2^(A/4)")
    _ensure(c0 + 2*D - 1 - A//4 == -3*c0 - 2*D - 4*k*k - 1,
            "third Weyl term exponent identity")
    _ensure(c0 + 2*D - 1 - A//4 < -2, "third Weyl term ratio < 1/4")
    _ensure(_leq_times_pow2(factorial(k), 1, k*k), "factorial upper bound")
    _ensure(k*k + c0 + 2*D + 4 <= A//2, "V <= 2^(A/2)")
    _ensure(B == 2*D + 8, "R exponent in conditional contradiction bound")
    result = {**b, "K": K, "U": b["c"] + b["e"], "recurrence_A": A,
              "recurrence_B": B, "density_D": density_exponent(k), "checks_passed": True}
    if k >= 3:
        prev = partition_budget(k - 1)
        previous_K = source_constant(k - 1)
        m = k*B + 1
        H = (prev["c"] + prev["e"], prev["e"])
        R = (k + 7 + k*H[0], 1 + k*H[1])
        T = (A + B*R[0], B*R[1])
        _ensure((T[0] + H[0], T[1] + H[1]) == (b["c"], b["e"]),
                "formal monomial identity T*H = F_k(L)")
        _ensure(K == k*k*2**(2*k + 1)*previous_K, "successive K ratio")
        _ensure((k - 1)**2 <= 2**k, "squared elementary induction comparison")
        _ensure((k - 1)**(2*k) <= 2**(k*k), "divisor constant comparison")
        _ensure(D + k*k <= 2**(k*k), "remaining A terms comparison")
        _ensure(A <= 64*2**(k*k), "A_k coarse upper bound")
        _ensure(64*A <= K, "A_k <= K_k/64")
        _ensure(64*(k + 8)*B <= K, "second induction term <= K_k/64")
        _ensure(12*m*previous_K <= K, "m_k K_(k-1) <= K_k/12")
        U = A + (k + 8)*B + m*(prev["c"] + 2*prev["e"])
        _ensure(U == b["c"] + b["e"], "exact U recursion")
        _ensure(U <= A + (k + 8)*B + 2*m*(prev["c"] + prev["e"]),
                "U recursion majorant")
        _ensure(Q(1, 64) + Q(1, 64) + Q(1, 24) == Q(7, 96) < Q(1, 4),
                "uniform induction coefficient slack")
        result.update({"H_exponents": H, "R_exponents": R, "T_exponents": T,
                       "m": m, "uniform_induction_coefficient": Q(7, 96)})
    return result


def compact_budget_scale(k):
    """Return P_k = k! * 2**(k*(k+1)/2) exactly, for 2 <= k <= 32."""
    _integer(k, "degree", 2, MAX_K)
    return factorial(k)*2**(k*(k + 1)//2)


def compact_budget_diagnostics(kmax=12):
    """Finite certificate, normalized-product and deficit diagnostics.

    The eight certificate rows j=3..10 are always verified exactly. Degree
    rows and tail-ratio samples stop at kmax. The infinite-product and tail
    conclusions require the written universal proof; this program checks
    its rational constants and finite samples, not the universal tail.
    """
    _integer(kmax, "compact degree cap", 2, MAX_K)
    certificates = (6693877, 6633957, 5268450, 2832889,
                    954144, 191498, 22175, 1450)
    pi = {2: 1}
    parameters = {}
    for k in range(3, max(kmax, 10) + 1):
        p = recurrence_parameters(k)
        m = k*p["B"] + 1
        pi[k] = pi[k - 1]*m
        parameters[k] = {**p, "m": m}
    table = []
    for k, z in enumerate(certificates, 3):
        A = parameters[k]["A"]
        _ensure(z*pi[k] <= 100000*A < (z + 1)*pi[k], "compact finite certificate bracket")
        _ensure((100000*A)//pi[k] == z, "compact certificate exact floor")
        table.append({"k": k, "z": z, "A": A, "Pi": pi[k]})
    upper_first_seven = Q(sum(z + 1 for z in certificates[:7]), 100000)
    lower_all_eight = Q(sum(certificates), 100000)
    _ensure(upper_first_seven == Q(22596997, 100000) < Q(22597, 100),
            "certificate upper sum through nine")
    _ensure(lower_all_eight == Q(22598440, 100000) > Q(11299, 50),
            "certificate lower sum through ten")
    _ensure(Q(certificates[-1] + 1, 100000) < Q(3, 200), "first tail term certificate")
    certified_tail_majorant = Q(8, 7)*Q(3, 200)
    _ensure(226 - Q(22597, 100) - certified_tail_majorant == Q(9, 700),
            "conditional infinite-tail deficit lower constant")
    _ensure(226 - Q(11299, 50) == Q(1, 50), "limiting deficit upper constant")
    E_majorant = 38 + Q(16, 49) + Q(97, 4*49*96)
    _ensure(Q(97, 18816) < Q(1, 147), "normalized exponent sum rational slack")
    _ensure(E_majorant < Q(115, 3), "normalized exponent majorant")
    q7 = Q(pi[7], compact_budget_scale(7))
    _ensure(q7 == Q(18772640957, 64424509440) < Q(7, 24), "exact normalized product at seven")
    _ensure(18772640957 < 18790481920, "integer q7 certificate")
    _ensure(38*q7 > 11, "lower constant for the written limiting exponent")
    _ensure(Q(1, 50)/38 == Q(1, 1900), "limiting gamma lower bracket constant")
    _ensure(Q(9, 700)/Q(115, 3) == Q(27, 80500), "limiting gamma upper bracket constant")
    tail_sum_cap = Q(65, 1024)
    _ensure((8 + Q(1, 8))*Q(1, 128) == tail_sum_cap, "geometric product-tail constant")
    q_majorant = Q(7, 24)/(1 - tail_sum_cap)
    _ensure(q_majorant == Q(896, 2877), "normalized product majorant constant")
    combined = q_majorant*Q(115, 3)
    _ensure(combined == Q(103040, 8631) < 12, "compact exponent coefficient")
    rows = []
    E, a_sum, d_product, tail_sum, tail_product = Q(38), Q(0), Q(1), Q(0), Q(1)
    previous_deficit = 226
    ratio_cases = 0
    for k in range(2, kmax + 1):
        b = partition_budget(k)
        P = compact_budget_scale(k)
        _ensure(P*P*2**(k + 1) == source_constant(k), "squared square-root-scale identity")
        if k >= 3:
            p = parameters[k]
            B, A, m = p["B"], p["A"], p["m"]
            E += Q(B, pi[k])
            a_sum += Q(A, pi[k])
            d = Q(8*k + 1, k*2**k)
            d_product *= 1 + d
            _ensure(Q(B, m) < Q(1, k), "normalized inhomogeneous summand bound")
            _ensure(m > (k - 1)*recurrence_parameters(k - 1)["B"] + 1,
                    "multipliers increase")
            if k >= 8:
                tail_sum += d
                tail_product *= 1 + d
            deficit = (k + 7)*b["e"] - b["c"]
            _ensure(deficit == m*previous_deficit - A, "coefficient deficit recursion")
        else:
            deficit = 226
            _ensure((k + 7)*b["e"] - b["c"] == deficit, "coefficient deficit base")
        previous_deficit = deficit
        q = Q(pi[k], P)
        _ensure(q == d_product/16, "normalized product identity")
        _ensure(Q(b["e"], pi[k]) == E < E_majorant, "exact normalized exponent recursion")
        normalized_deficit = Q(deficit, pi[k])
        _ensure(normalized_deficit == 226 - a_sum > Q(9, 700), "finite normalized deficit")
        if k >= 10:
            _ensure(normalized_deficit < Q(1, 50), "finite deficit upper bound after ten")
        _ensure(tail_sum <= tail_sum_cap < 1, "finite product-tail sum")
        _ensure(tail_product <= 1/(1 - tail_sum), "finite product-geometric inequality")
        if k >= 7:
            _ensure(q == q7*tail_product, "normalized product split at seven")
        else:
            _ensure(q <= q7, "initial normalized products bounded by q7")
        _ensure(q < q_majorant and Q(b["e"], P) == q*E < combined < 12,
                "finite compact exponent bound")
        _ensure(b["c"] < (k + 7)*b["e"] < 12*(k + 7)*P,
                "finite compact coefficient bound")
        _ensure(b["c"] + b["e"] < 12*(k + 8)*P, "finite compact total budget")
        C, exponent = 12*(k + 7)*P, 12*P
        _ensure(C + exponent + 4 == (k + 8)*(exponent + 1) - (k + 4),
                "compact density-bound rewrite exponent identity")
        if k >= 10:
            j = k - 1
            current, previous = parameters[k], parameters[j]
            denominator = current["m"]
            ratio = Q(current["A"], previous["A"]*denominator)
            _ensure(ratio < Q(1, 8), "finite tail-ratio sample")
            _ensure(Q(2, denominator) < Q(1, 8), "linear-power summand ratio")
            _ensure(Q(k*k, j*j*denominator) < Q(2, denominator), "quadratic summand ratio")
            middle_ratio = Q(j*j, denominator)*Q(j, j - 1)**(2*j)
            _ensure(Q(j, j - 1)**(j - 1) < 3, "finite binomial comparison sample")
            _ensure(Q(j, j - 1)**(2*j) < 9*Q(j, j - 1)**2 <= 9*Q(9, 8)**2 < 12,
                    "middle summand ratio constant")
            _ensure(middle_ratio < Q(12*j, 2**(j + 1)) <= Q(27, 256) < Q(1, 8),
                    "middle summand geometric-tail sample")
            _ensure(Q(j + 1, 2**(j + 2)) <= Q(j, 2**(j + 1)), "tail envelope decrease")
            ratio_cases += 1
        rows.append({"k": k, "P": P, "Pi": pi[k], "normalized_product": q,
                     "normalized_exponent": E, "normalized_deficit": normalized_deficit,
                     "e_over_P": Q(b["e"], P)})
    return {"kmax": kmax, "finite_degree_rows": rows, "finite_certificate_table": table,
            "finite_certificate_rows": len(table), "finite_tail_ratio_samples": ratio_cases,
            "q7": q7, "normalized_exponent_majorant": E_majorant,
            "normalized_product_majorant": q_majorant, "combined_exponent_majorant": combined,
            "certificate_upper_sum_through_nine": upper_first_seven,
            "certificate_lower_sum_through_ten": lower_all_eight,
            "limiting_deficit_constants_requiring_written_tail_proof": (Q(9, 700), Q(1, 50)),
            "universal_tail_proved_by_program": False,
            "scope": "exact finite certificate and finite algebra; universal product and tail estimates require the written proof"}


def _root_floor(value, exponent):
    if value <= 1 or exponent >= value.bit_length():
        return int(value > 0)
    low, high = 0, 1 << ((value.bit_length() + exponent - 1)//exponent)
    while low + 1 < high:
        mid = (low + high)//2
        if mid**exponent <= value:
            low = mid
        else:
            high = mid
    return high if high**exponent <= value else low


def exact_budget_length(N, M, c, e):
    """max(1,floor((3*N/(8*M*2**c))**(1/(e+1)))) with exact rounding.

    N,M have at most 1024 bits; c,e are capped symbolic exponents. A bit-length
    shortcut prevents enormous 2**c or high-degree powers being materialized.
    """
    _integer(N, "N", 1, MAX_RATIO)
    _integer(M, "M", 1, N)
    _integer(c, "c", 0, MAX_SYMBOLIC_EXPONENT)
    _integer(e, "e", 2, MAX_SYMBOLIC_EXPONENT)
    quotient = (3*N)//(8*M)
    if c >= quotient.bit_length():
        return 1
    return max(1, _root_floor(quotient >> c, e + 1))


def source_bridge_length(N, M, k):
    """Exact ceil((N/M)**(1/D_k)/8), capped without floating-point roots.

    Large D_k immediately yields a singleton at these bounded input scales;
    no enormous power is expanded merely to establish that fact.
    """
    _integer(N, "N", 1, MAX_RATIO)
    _integer(M, "M", 1, N)
    _integer(k, "degree", 1, MAX_K)
    D = density_exponent(k)
    root = _root_floor(N//M, D)
    candidate = root//8
    if candidate == 0:
        return 1
    return candidate if M*(8*candidate)**D == N else candidate + 1


def ordered_divisor_count(r, m):
    """Count ordered r-factorizations by prime factors, for r<=8,m<=4096."""
    _integer(r, "factor count", 1, 8)
    _integer(m, "product", 1, MAX_LENGTH)
    left, p, count = m, 2, 1
    while p*p <= left:
        a = 0
        while left % p == 0:
            left //= p
            a += 1
        count *= comb(a + r - 1, r - 1)
        p += 1
    if left > 1:
        count *= r
    return count


@lru_cache(maxsize=2048)
def _direct_divisor_count(r, m):
    if r == 1:
        return 1
    return sum(_direct_divisor_count(r - 1, m//d) for d in range(1, m + 1) if m % d == 0)


def divisor_diagnostics(rmax=6, mmax=48):
    """Finite divisor/composition checks; the analytic bound is not inferred."""
    _integer(rmax, "rmax", 1, 8)
    _integer(mmax, "mmax", 1, 128)
    cases = compositions = 0
    for r in range(1, rmax + 1):
        c = 3*r**(2*r + 2)
        for a in range(33):
            _ensure(comb(a + r - 1, r - 1) <= r**a, "weak compositions <= words")
            _ensure(comb(a + r - 1, r - 1) <= (a + 1)**r, "box bound for compositions")
            b, s = divmod(a, 2*r*r)
            _ensure(0 <= s < 2*r*r, "small-prime exponent decomposition")
            _ensure(b + 1 <= 2**b, "linear versus binary growth")
            _ensure((a + 1)**r <= (2*r*r)**r * 2**(r*b), "small-prime local bound")
            _ensure((2*r*r)**r <= 2**(3*r*r), "small-prime constant")
            compositions += 1
        for m in range(1, mmax + 1):
            count = ordered_divisor_count(r, m)
            _ensure(count == _direct_divisor_count(r, m), "multiplicative versus direct ordered factors")
            _ensure(_leq_times_pow2(count**(2*r), m, 2*r*c), "powered divisor bound")
            cases += 1
    return {"ordered_factor_cases": cases, "composition_cases": compositions,
            "rmax": rmax, "mmax": mmax, "huge_divisor_constant_materialized": False}


def _eval(coefficients, x):
    result = Q(0)
    for coefficient in reversed(coefficients):
        result = result*x + coefficient
    return result


def _compose(coefficients, start, step):
    return tuple(sum((coefficients[j]*comb(j, i)*start**(j - i)*step**i
                      for j in range(i, len(coefficients))), Q(0))
                 for i in range(len(coefficients)))


def compose_polynomial(coefficients, start, step):
    """Exact coefficients of P(start+step*t), degree at most eight."""
    coefficients = _coefficients(coefficients)
    _integer(start, "start", -MAX_LENGTH, MAX_LENGTH)
    _integer(step, "step", -MAX_LENGTH, MAX_LENGTH)
    return _compose(coefficients, start, step)


def difference_polynomial(coefficients, shifts):
    """Exact iterated forward differences, retaining zero coefficient slots."""
    coefficients = _coefficients(coefficients)
    if type(shifts) not in (tuple, list) or not 1 <= len(shifts) <= MAX_POLY_DEGREE:
        raise ValueError("shifts must be a list or tuple of length 1..8")
    for shift in shifts:
        _integer(shift, "shift", -16, 16)
    for shift in shifts:
        translated = _compose(coefficients, shift, 1)
        coefficients = tuple(a - b for a, b in zip(translated, coefficients))
    return coefficients


def differencing_diagnostics(kmax=8):
    """Check exact coefficients and independent subset-expansion identities."""
    _integer(kmax, "polynomial degree cap", 2, MAX_POLY_DEGREE)
    cases = evaluations = exponent_cases = 0
    for k in range(2, kmax + 1):
        coefficients = tuple(Q((-1)**j*(j + 1), j + 2) for j in range(k + 1))
        for shift_value in (0, 1, -2, 3):
            shifts = (shift_value,) + tuple(1 + (j % 2) for j in range(k - 2))
            diff = difference_polynomial(coefficients, shifts)
            expected = factorial(k)*coefficients[k]
            for shift in shifts:
                expected *= shift
            _ensure(diff[1] == expected and all(x == 0 for x in diff[2:]),
                    "(k-1)-fold difference has coefficient k! omega product(h)")
            for x in (-2, 0, 3):
                direct = Q(0)
                for choices in product((0, 1), repeat=len(shifts)):
                    sign = (-1)**(len(shifts) - sum(choices))
                    direct += sign*_eval(coefficients, x + sum(a*b for a, b in zip(choices, shifts)))
                _ensure(_eval(diff, x) == direct, "independent subset expansion")
                evaluations += 1
            cases += 1
        for j in range(1, k):
            exponent = 2**j - j - 1
            _ensure(2*exponent + j == 2**(j + 1) - j - 2,
                    "Cauchy-Schwarz prefactor induction identity")
            exponent_cases += 1
    return {"coefficient_cases": cases, "subset_expansion_evaluations": evaluations,
            "differencing_prefactor_cases": exponent_cases,
            "scope": "finite algebra only; no complex Weyl-sum bound numerically certified"}


def chunk_lengths(size, target):
    """Partition size>=target into target..2*target-1 blocks, no empty tail."""
    _integer(size, "size", 1, MAX_LENGTH)
    _integer(target, "target", 1, size)
    count, tail = divmod(size, target)
    return (target,)*(count - 1) + (target + tail,)


def residue_chunks(n, step, H):
    """Partition bounded indices by residue chains, then H..2H-1 chunks."""
    _integer(n, "n", 1, MAX_LENGTH)
    _integer(step, "recurrence step", 1, n)
    _integer(H, "H", 1, n)
    if n < step*H:
        raise ValueError("n >= step*H is required so every residue chain has H terms")
    cells = []
    for residue in range(step):
        chain = tuple(range(residue, n, step))
        offset = 0
        for size in chunk_lengths(len(chain), H):
            cells.append(chain[offset:offset + size])
            offset += size
    _ensure(sorted(x for cell in cells for x in cell) == list(range(n)), "residue partition coverage")
    return tuple(cells)


def localization_structure(n, step, H, L):
    """Toy target-2L refinement and resplitting, with exact coverage only.

    The inner refinement here is a structural contiguous partition. It is not
    an invocation, construction or numerical certificate of the phase lemma.
    """
    _integer(n, "n", 1, MAX_LENGTH)
    _integer(step, "step", 1, n)
    _integer(H, "H", 1, n)
    _integer(L, "L", 1, n)
    if H < 2*L:
        raise ValueError("H >= 2L is needed for this bounded structural toy")
    outer = residue_chunks(n, step, H)
    result = []
    inner_sizes = []
    for outer_cell in outer:
        cursor = 0
        for size in chunk_lengths(len(outer_cell), 2*L):
            inner = outer_cell[cursor:cursor + size]
            cursor += size
            inner_sizes.append(size)
            offset = 0
            for final_size in chunk_lengths(size, L):
                result.append(inner[offset:offset + final_size])
                offset += final_size
    _ensure(sorted(x for cell in result for x in cell) == list(range(n)), "refinement partitions parent")
    _ensure(all(L <= len(cell) < 2*L for cell in result), "final cell size interval")
    _ensure(all(all(b - a == step for a, b in zip(cell, cell[1:])) for cell in result),
            "final cells are index arithmetic progressions")
    return {"cells": tuple(result), "outer_lengths": tuple(map(len, outer)),
            "inner_lengths": tuple(inner_sizes), "phase_error_certified": False}


def restriction_diagnostic(coefficients, start, step, terms):
    """Remove the integer leading coefficient after restriction; exact mod 1.

    Reports a rational turn-error majorant, not a claim that the required
    recurrence or localization error is attained for arbitrary toy inputs.
    """
    coefficients = _coefficients(coefficients)
    _integer(start, "start", -MAX_LENGTH, MAX_LENGTH)
    _integer(step, "step", -MAX_LENGTH, MAX_LENGTH)
    _integer(terms, "terms", 1, MAX_LENGTH)
    k = len(coefficients) - 1
    if k < 1:
        raise ValueError("restriction diagnostic requires positive displayed degree")
    restricted = _compose(coefficients, start, step)
    epsilon = _centered(restricted[-1])
    integer_part = restricted[-1] - epsilon
    _ensure(integer_part.denominator == 1, "leading integer coefficient")
    lower = restricted[:-1]
    for t in range(terms):
        original = _eval(coefficients, start + step*t)
        reduced = epsilon*t**k + _eval(lower, t)
        _ensure((original - reduced).denominator == 1, "integer term disappears mod one")
        _ensure(original - reduced == integer_part*t**k, "exact restriction decomposition")
    return {"raw_leading_coefficient": restricted[-1], "integer_part": integer_part,
            "epsilon": epsilon, "lower_coefficients": lower,
            "turn_error_majorant": abs(epsilon)*(terms - 1)**k,
            "tested_terms": terms}


def modular_restriction_diagnostic(N, start, step, n, coefficients):
    """Check wrapped nonunit proper parents without any modular division."""
    _integer(N, "modulus", 1, MAX_MODULUS)
    _integer(start, "start", 0, N - 1)
    _integer(step, "step", 0, N - 1)
    _integer(n, "parent length", 1, N)
    coefficients = _coefficients(coefficients)
    if any(c.denominator != 1 or not 0 <= c < N for c in coefficients):
        raise ValueError("modular coefficients must be integer residues")
    if n > N//gcd(step, N):
        raise ValueError("the displayed modular parent must be proper")
    lifted = _compose(tuple(c/N for c in coefficients), start, step)
    points = tuple((start + step*j) % N for j in range(n))
    for j, x in enumerate(points):
        modular_value = (_eval(coefficients, x) % N)/N
        _ensure((_eval(lifted, j) - modular_value).denominator == 1, "coefficient phase lift through wrap")
    return {"points": points, "lifted_coefficients": lifted, "proper": len(set(points)) == n,
            "nonunit_step": gcd(step, N) != 1}


def rational_recurrence_witness(k, denominator, numerator, R):
    """Finite rational sample: search only p<=denominator, never up to T.

    p=denominator always makes the phase integral. This rational observation
    provides no uniform recurrence certificate for arbitrary real theta.
    """
    _integer(k, "degree", 2, MAX_K)
    _integer(denominator, "denominator", 1, MAX_DENOMINATOR)
    _integer(numerator, "numerator", 0, denominator - 1)
    _integer(R, "R", 2, MAX_R)
    for p in range(1, denominator + 1):
        residue = (numerator*pow(p, k, denominator)) % denominator
        norm = Q(min(residue, denominator - residue), denominator)
        if norm < Q(1, R):
            return {"p": p, "norm": norm, "strict_target": Q(1, R),
                    "search_cap": denominator, "all_real_certificate": False}
    raise CheckFailure("rational denominator witness must exist")


def coset_pair_moment(n, selected, difference):
    """Exact pair moment for uniform (a,d), including nonunit differences."""
    _integer(n, "modulus", 2, MAX_MODULUS)
    _integer(difference, "difference", 1, n - 1)
    selected = _subset(n, selected)
    g = gcd(n, difference)
    counts = tuple(sum(x % g == residue for x in selected) for residue in range(g))
    direct = Q(sum((x + difference*d) % n in selected for x in selected for d in range(n)), n*n)
    coset = Q(g*sum(c*c for c in counts), n*n)
    delta = Q(len(selected), n)
    _ensure(direct == coset and coset >= delta*delta, "subgroup pair moment identity and covariance")
    return {"pair_expectation": direct, "coset_expectation": coset,
            "covariance": coset - delta*delta, "coset_counts": counts,
            "subgroup_size": n//g}


def all_step_moments(n, selected, L):
    """Exact all-direction moments with repeated samples and bad steps kept."""
    _integer(n, "modulus", 2, MAX_MODULUS)
    _integer(L, "length", 1, n)
    selected = _subset(n, selected)
    delta = Q(len(selected), n)
    good_sums, bad_sums = [], []
    good_d = bad_d = 0
    for d in range(n):
        values = [sum((a + j*d) % n in selected for j in range(L)) for a in range(n)]
        _ensure(sum(values) == len(selected)*L, "each direction has the same mean")
        if n//gcd(n, d) >= L:
            good_sums.extend(values)
            good_d += 1
        else:
            bad_sums.extend(values)
            bad_d += 1
    _ensure(good_d > 0, "a proper direction exists")
    eta = Q(bad_d, n)
    _ensure(2*bad_d <= L*(L - 1), "union of multiplication kernels")
    good_var = Q(sum(x*x for x in good_sums), n*good_d*L*L) - delta*delta
    bad_var = Q(sum(x*x for x in bad_sums), n*bad_d*L*L) - delta*delta if bad_d else Q(0)
    variance = Q(sum(x*x for x in good_sums + bad_sums), n*n*L*L) - delta*delta
    covariance_sum = Q(0)
    for h in range(1, L):
        g = gcd(h, n)
        counts = [0]*g
        for x in selected:
            counts[x % g] += 1
        covariance = Q(g*sum(c*c for c in counts), n*n) - delta*delta
        _ensure(covariance >= 0, "nonnegative off-diagonal covariance")
        covariance_sum += (L - h)*covariance
    expected = delta*(1 - delta)/L + 2*covariance_sum/(L*L)
    _ensure(variance == expected, "all-step variance equals subgroup formula")
    _ensure(variance == (1 - eta)*good_var + eta*bad_var, "conditional variance mixture")
    _ensure(bad_var <= delta*(1 - delta), "bad direction variance bound")
    h = Q(max(good_sums), L) - delta
    _ensure(good_var <= delta*h, "one-sided proper direction variance bound")
    lower = None
    applies = bool(selected and n >= L**3)
    if selected:
        lower = (1 - delta)*(Q(1, L) - eta)/(1 - eta)
        _ensure(h >= lower, "bad-direction discard gain")
    if applies:
        _ensure(eta < Q(1, 2*L), "strict bad fraction under N>=L^3")
        _ensure(h >= (1 - delta)/(2*L), "simplified proper progression gain")
    return {"mean": delta, "variance": variance, "coset_variance": expected,
            "good_variance": good_var, "bad_variance": bad_var if bad_d else None,
            "good_steps": good_d, "bad_steps": bad_d, "bad_fraction": eta,
            "maximum_proper_gain": h, "discard_gain_lower_bound": lower,
            "simplified_gain_applies": applies}


def cover_mass(n, selected, union):
    """Exact signed/absolute mass identities when A is contained in U."""
    _integer(n, "modulus", 2, MAX_MODULUS)
    selected, union = _subset(n, selected), _subset(n, union)
    if not selected <= union:
        raise ValueError("the parent union must cover A")
    delta, tau = Q(len(selected), n), Q(len(union), n)
    mu = sum((abs(Q(int(x in selected)) - delta) for x in union), Q(0))/n
    signed = sum((Q(int(x in selected)) - delta for x in union), Q(0))
    _ensure(mu == delta*(1 + tau - 2*delta), "cover absolute mass identity")
    _ensure(mu <= 2*delta*(1 - delta) <= 2*tau*(1 - delta) <= 2*(1 - delta), "cover mass bounds")
    _ensure(signed == delta*(n - len(union)) >= 0, "signed cover mass nonnegative")
    return {"density": delta, "union_density": tau, "mu": mu, "signed_mass": signed}


def rounding_and_assembly_diagnostics():
    """Finite exact rounding and scalar branch checks for density assembly."""
    floor_cases = ceiling_cases = mass_cases = 0
    for c, e in ((0, 2), (6, 3), (116, 38)):
        for L in (2, 3, 7):
            boundary = 8*2**c*L**(e + 1)
            _ensure(exact_budget_length(boundary - 1, 3, c, e) == L - 1, "floor immediately below boundary")
            _ensure(exact_budget_length(boundary, 3, c, e) == L, "floor at boundary")
            _ensure(exact_budget_length(boundary + 1, 3, c, e) == L, "floor immediately above boundary")
            S = Q(boundary, 3)
            _ensure(S >= L**3, "exact-budget scale suffices for variance")
            _ensure(3*S/(8*L) == 2**c*L**e, "exact-budget parent-length equality")
            floor_cases += 3
    for L in (1, 2, 7):
        for M in (1, 3):
            boundary = M*(8*L)**4
            _ensure(source_bridge_length(boundary - 1, M, 1) == L, "ceiling below boundary")
            _ensure(source_bridge_length(boundary, M, 1) == L, "ceiling at boundary")
            _ensure(source_bridge_length(boundary + 1, M, 1) == L + 1, "ceiling above boundary")
            ceiling_cases += 3
    # The scalar correlation values below are examples, not certifications of
    # a modular phase correlation premise. They test the proof's inequalities.
    for L in (2, 3, 8):
        delta, tau = Q(1, 2), Q(1)
        b = 1 - delta
        mu = delta*(1 + tau - 2*delta)
        low_alpha = 3*b/(2*L)
        _ensure(b/(2*L) == low_alpha/3, "variance branch includes equality")
        alpha = (low_alpha + mu)/2
        _ensure(low_alpha < alpha <= mu <= 2*tau*b <= 2*b, "large-correlation branch example")
        _ensure(tau > Q(3, 4*L), "union density forced by large correlation")
        error_majorant = mu/(4*L)
        _ensure(error_majorant <= b/(2*L) < alpha/3, "normalized phase error budget")
        _ensure(alpha - error_majorant > 2*alpha/3, "absolute cell mass after phase error")
        positive_cell_mass = (alpha - error_majorant + delta*(1 - tau))/2
        _ensure(positive_cell_mass > alpha/3, "positive cell mass from nonnegative signed mass")
        mass_cases += 1
    return {"exact_floor_boundary_cases": floor_cases,
            "source_ceiling_boundary_cases": ceiling_cases,
            "scalar_large_correlation_cases": mass_cases,
            "scalar_correlation_premises_are_examples_only": True}


def regression_diagnostics():
    """Named regressions for the all-degree proof's easy-to-lose distinctions."""
    general, sharp = partition_budget(3), partition_budget(3, True)
    _ensure((general["c"], general["e"]) == (10986, 1878), "general cubic budget")
    _ensure((sharp["c"], sharp["e"]) == (7834, 1878), "sharper cubic budget")
    _ensure(recurrence_parameters(3)["A"] == 3280, "general cubic recurrence")
    _ensure(recurrence_parameters(3, True)["A"] == 128, "separate cubic recurrence")
    _ensure(8189 > sharp["c"] and 4095 > sharp["e"], "separate cubic 1/4096 assembly")
    _ensure(96 > 64, "affine parent-length slack")
    chord = PI_UPPER/64 + Q(1, 8)
    _ensure(chord < Q(3, 16) < Q(1, 4), "localization chord budget using pi<22/7")
    strict = rational_recurrence_witness(3, 2, 1, 2)
    _ensure(strict["p"] == 2, "equality at 1/R is not a recurrence witness")
    integer_leading = restriction_diagnostic((0, Q(1, 7), 0, Q(1, 8)), 5, 2, 5)
    _ensure(integer_leading["epsilon"] == 0, "integer leading phase disappears")
    wrapped = modular_restriction_diagnostic(12, 11, 4, 3, (5, 7, 3, 2, 11))
    _ensure(wrapped["points"] == (11, 3, 7), "nonunit wrapping parent")
    nonunit = coset_pair_moment(4, {0, 2}, 2)
    _ensure(nonunit["covariance"] == Q(1, 4), "nonunit covariance must not be set to zero")
    repeated = all_step_moments(4, {0, 2}, 3)
    _ensure(repeated["variance"] == Q(5, 36), "bad copies are multisets, not sets")
    _ensure(chunk_lengths(11, 6) == (11,), "refinement at L can fail the required 2L threshold")
    try:
        localization_structure(11, 1, 6, 4)
    except ValueError:
        target_two_L_guard = True
    else:
        raise CheckFailure("target-2L guard must reject insufficient H")
    # Exact rational equality demonstrates why the first Dirichlet comparison
    # must be weak, as explained in the article's cubic recurrence proof;
    # the following bound is strict.
    p, T, R, r = 2, 32, 2, 2
    beta_q = Q(1, T**r)
    lhs = _centered(p**r*beta_q)
    _ensure(lhs == Q(p, T)**r < Q(1, R), "weak Dirichlet comparison can be equality")
    return {"general_cubic": general, "sharper_cubic": sharp,
            "combined_chord_coefficient_using_pi_lt_22_over_7": chord,
            "strict_recurrence_boundary_witness": strict,
            "integer_leading_restriction": integer_leading,
            "wrapped_nonunit_points": wrapped["points"],
            "nonunit_covariance": nonunit["covariance"],
            "repeated_copy_variance": repeated["variance"],
            "target_2L_guard_active": target_two_L_guard,
            "dirichlet_first_comparison_can_be_equality": True,
            "conditional_p_lt_T_over_R_squared_is_not_the_unconditional_statement": True}


def run_checks(nmax=6, kmax=12):
    """Run bounded deterministic diagnostics; exhaustive modulus cap is eight."""
    _integer(nmax, "nmax", 2, MAX_NMAX)
    _integer(kmax, "kmax", 3, MAX_K)
    moments = pairs = cover_cases = kernel_cases = recurrence_cases = structure_cases = 0
    for n in range(2, nmax + 1):
        for mask in range(1 << n):
            selected = {x for x in range(n) if mask & (1 << x)}
            for L in range(1, min(n, 4) + 1):
                all_step_moments(n, selected, L)
                moments += 1
            for h in range(1, n):
                coset_pair_moment(n, selected, h)
                pairs += 1
        for labels in product(range(3), repeat=n):
            cover_mass(n, {j for j, label in enumerate(labels) if label == 2},
                       {j for j, label in enumerate(labels) if label != 0})
            cover_cases += 1
        for h in range(1, n):
            _ensure(sum(h*d % n == 0 for d in range(n)) == gcd(h, n) <= h, "multiplication kernel")
            kernel_cases += 1
        for k in range(2, min(kmax, 8) + 1):
            for numerator in range(n):
                rational_recurrence_witness(k, n, numerator, 2*n)
                recurrence_cases += 1
    selected_large = []
    for n, L in ((8, 2), (27, 3), (64, 4)):
        for selected in ({0}, set(range(0, n, 2)), set(range(n))):
            selected_large.append({"N": n, "L": L, "subset_size": len(selected),
                                   **all_step_moments(n, selected, L)})
    for n in range(4, 49):
        for L in (1, 2, 3):
            for step in (1, 2, 3):
                H = 2*L
                if n >= step*H:
                    localization_structure(n, step, H, L)
                    structure_cases += 1
    restrictions = []
    for k in range(2, 9):
        coefficients = tuple(Q((-1)**j, j + 2) for j in range(k + 1))
        restrictions.append({"degree": k, **restriction_diagnostic(coefficients, 3, -2, 9)})
    return _jsonable({
        "report": 277, "arithmetic": "integers and exact Fractions only",
        "finite_diagnostics_not_proofs": True,
        "parameters": {"nmax": nmax, "kmax": kmax, "hard_nmax_cap": MAX_NMAX,
                       "hard_kmax_cap": MAX_K},
        "budgets": [budget_diagnostic(k) for k in range(2, kmax + 1)],
        "uniform_all_k_status": "finite algebra diagnostics only; the article supplies the universal induction",
        "compact_budget_growth": compact_budget_diagnostics(kmax),
        "divisors": divisor_diagnostics(),
        "differencing": differencing_diagnostics(),
        "finite_variance": {"all_subset_length_instances": moments,
                            "all_subset_difference_instances": pairs,
                            "kernel_cases": kernel_cases, "selected_larger_cases": selected_large},
        "cover_mass": {"all_A_subset_U_pairs": cover_cases},
        "residue_localization": {"structural_toy_instances": structure_cases,
                                 "restriction_examples": restrictions,
                                 "theorem_scale_partition_enumerated": False,
                                 "phase_error_certified_by_toys": False},
        "rational_recurrence_samples": {"cases": recurrence_cases, "all_real_certificate": False},
        "rounding_and_assembly": rounding_and_assembly_diagnostics(),
        "regressions": regression_diagnostics(),
        "limitations": [
            "Finite diagnostics are not proofs of real-coefficient recurrence or of the density theorem.",
            "Finite degree checks do not establish an all-k induction; consult the written proof.",
            "Large recurrence and partition thresholds are represented symbolically; no theorem-scale partition is enumerated.",
            "No numerical complex exponential, trigonometric, logarithmic or floating-point root checks are used.",
            "The sharper cubic constants are a separate specialization, not the general recurrence constants.",
            "No Lean verification, priority claim or global Ramsey/Szemeredi improvement is asserted."]})


def main(argv=None):
    """CLI: --nmax 2..8, --kmax 3..32, --full (defaults 8 and 32)."""
    if argv is None:
        argv = sys.argv[1:]
    if type(argv) not in (list, tuple) or len(argv) > 5 or any(
            type(arg) is not str or len(arg) > DIGIT_CAP for arg in argv):
        raise ValueError("CLI accepts at most five arguments of at most 64 characters")
    parser = argparse.ArgumentParser(description=__doc__)
    def option(name, low, high):
        def convert(value):
            try:
                return _parse(value, name, low, high)
            except ValueError as exc:
                raise argparse.ArgumentTypeError(str(exc)) from exc
        return convert
    parser.add_argument("--nmax", type=option("nmax", 2, MAX_NMAX))
    parser.add_argument("--kmax", type=option("kmax", 3, MAX_K))
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args(argv)
    result = run_checks(args.nmax if args.nmax is not None else (8 if args.full else 6),
                        args.kmax if args.kmax is not None else (32 if args.full else 12))
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
