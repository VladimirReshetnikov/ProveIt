import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Exact, standard-library-only replay of Report138's finite mathematics.

This module does not import the investigation or audit implementations. Sources
are data arrays only. Importing it or calling ``run`` never reads/writes files.
All test failures use explicit exceptions and remain active under python -O.
Finite checks are evidence for the formulas, not substitutes for their proofs.
"""

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb, factorial
from typing import Any, Sequence

Partition = tuple[int, ...]
Boundary = tuple[int, int, int, int]
TAUS: tuple[Partition, ...] = ((), (1,), (2,), (1, 1), (2, 1), (2, 2))


class ReplayError(ValueError):
    """A claimed exact identity failed, or supplied source data were invalid."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReplayError(message)


@lru_cache(maxsize=None)
def partitions(n: int, rows: int = 4, largest: int | None = None) -> tuple[Partition, ...]:
    """Partitions in descending lexicographic order, with at most ``rows`` parts."""
    if n < 0 or rows < 0:
        return ()
    if n == 0:
        return ((),)
    if rows == 0:
        return ()
    top = n if largest is None else min(n, largest)
    return tuple((a,) + tail for a in range(top, 0, -1)
                 for tail in partitions(n - a, rows - 1, a))


@lru_cache(maxsize=None)
def signed_permutations(n: int) -> tuple[tuple[tuple[int, ...], int], ...]:
    return tuple((p, -1 if sum(p[i] > p[j] for i in range(n)
                              for j in range(i + 1, n)) % 2 else 1)
                 for p in permutations(range(n)))


@lru_cache(maxsize=None)
def skew_determinant(outer: Partition, inner: Partition) -> int:
    """Aitken's factorial determinant, expanded into integer multinomials."""
    if len(inner) > len(outer) or any(b > a for a, b in zip(outer, inner)):
        return 0
    q = sum(outer) - sum(inner)
    h = len(outer)
    padded = inner + (0,) * (h - len(inner))
    numerator = factorial(q)
    answer = 0
    for perm, sign in signed_permutations(h):
        degrees = tuple(outer[i] - padded[perm[i]] - i + perm[i] for i in range(h))
        if min(degrees, default=0) < 0:
            continue
        denominator = 1
        for d in degrees:
            denominator *= factorial(d)
        quotient, remainder = divmod(numerator, denominator)
        require(remainder == 0, "Nonintegral determinant multinomial")
        answer += sign * quotient
    require(answer >= 0, "Negative standard skew tableau number")
    return answer


@lru_cache(maxsize=None)
def skew_young_removal(outer: Partition, inner: Partition) -> int:
    """Independent Young-lattice corner-removal recurrence."""
    if len(inner) > len(outer) or any(b > a for a, b in zip(outer, inner)):
        return 0
    if outer == inner:
        return 1
    answer = 0
    for row, value in enumerate(outer):
        below = outer[row + 1] if row + 1 < len(outer) else 0
        floor = inner[row] if row < len(inner) else 0
        if value > max(below, floor):
            child = outer[:row] + (value - 1,) + outer[row + 1:]
            child = tuple(x for x in child if x)
            answer += skew_young_removal(child, inner)
    return answer


def transpose(shape: Partition) -> Partition:
    return tuple(sum(a >= col for a in shape) for col in range(1, max(shape, default=0) + 1))


def gl2_product(left: Partition, right: Partition) -> tuple[Partition, ...]:
    """The multiplicity-one GL(2) Clebsch-Gordan rule."""
    require(len(left) <= 2 and len(right) <= 2, "GL(2) input has more than two rows")
    u, v = (left + (0, 0))[:2]
    c, d = (right + (0, 0))[:2]
    return tuple(tuple(x for x in (u + c - r, v + d + r) if x)
                 for r in range(min(u - v, c - d) + 1))


@lru_cache(maxsize=None)
def gl2_adjoint(P: int, R: int, tau: Partition) -> tuple[tuple[Partition, int], ...]:
    """Schur coefficients of s_tau^perp G_(P,R), in two variables."""
    out = []
    for nu in partitions(P - sum(tau), 2):
        coefficient = sum(skew_determinant(alpha, (R,)) for alpha in gl2_product(nu, tau))
        if coefficient:
            out.append((nu, coefficient))
    return tuple(out)


def boundary_parameters(m: int) -> tuple[Boundary, ...]:
    return tuple((P, R, Q, T) for P in range(1, m)
                 for Q in range(1, m - P + 1)
                 for R in range(1, P + 1) for T in range(1, Q + 1))


def six_term_table(m: int) -> dict[Boundary, int]:
    """All supported D_m at once, reusing coefficient vectors per boundary.

    Each vector is evaluated independently from the factorial determinant.
    No H, D, or U values from sources are used in the computation.
    """
    keys = boundary_parameters(m)
    table = dict.fromkeys(keys, 0)
    for tau in TAUS:
        k = sum(tau)
        if 2 * k > m:
            continue
        outer_shapes = partitions(m - k, 4)
        vectors: dict[tuple[int, int, Partition], tuple[int, ...]] = {}
        for eta in dict.fromkeys((tau, transpose(tau))):
            for P in range(max(1, k), m):
                for R in range(1, P + 1):
                    coefficients = gl2_adjoint(P, R, eta)
                    if coefficients:
                        vectors[P, R, eta] = tuple(
                            sum(c * skew_determinant(rho, nu) for nu, c in coefficients)
                            for rho in outer_shapes)
        sign = -1 if k % 2 else 1
        conjugate = transpose(tau)
        for P, R, Q, T in keys:
            a = vectors.get((P, R, tau))
            b = vectors.get((Q, T, conjugate))
            if a is not None and b is not None:
                table[P, R, Q, T] += sign * sum(x * y for x, y in zip(a, b))
    require(all(value >= 0 for value in table.values()), f"Negative D_{m}")
    return table


def longest_increasing(word: Sequence[int]) -> int:
    """Small-permutation quadratic dynamic program, independent of RSK."""
    ending: list[int] = []
    for i, value in enumerate(word):
        ending.append(1 + max((ending[j] for j in range(i) if word[j] < value), default=0))
    return max(ending, default=0)


def boundary_enumeration(m: int, predicted: dict[Boundary, int]) -> dict[str, Any]:
    observed = dict.fromkeys(boundary_parameters(m), 0)
    avoiders = 0
    for word in permutations(range(1, m + 1)):
        if longest_increasing(word) > 4:
            continue
        avoiders += 1
        suffix = [0] + [longest_increasing(word[-P:]) for P in range(1, m + 1)]
        low = [0] + [longest_increasing(tuple(x for x in word if x <= Q))
                     for Q in range(1, m + 1)]
        for P in range(1, m):
            if suffix[P] > 2:
                continue
            for Q in range(1, min(m - P, min(word[-P:]) - 1) + 1):
                if low[Q] > 2:
                    continue
                for R in range(1, P + 1):
                    if suffix[R] != 1:
                        continue
                    for T in range(1, Q + 1):
                        if low[T] == 1:
                            observed[P, R, Q, T] += 1
    counts = []
    for (P, R, Q, T), actual in observed.items():
        expected = predicted[P, R, Q, T]
        require(actual == expected, f"Boundary mismatch m={m}, parameters={(P,R,Q,T)}")
        counts.append(dict(P=P, R=R, Q=Q, T=T, direct=actual, six_term=expected))
    return dict(m=m, permutations=factorial(m), avoiders=avoiders,
                parameter_tests=len(counts), counts=counts, status="PASS")


def row_insert(word: Sequence[int]) -> tuple[list[list[int]], list[list[int]]]:
    """Ordinary standard RSK, using a linear first-greater search."""
    insertion: list[list[int]] = []
    recording: list[list[int]] = []
    for label, initial in enumerate(word, 1):
        value = initial
        for r, row in enumerate(insertion):
            pos = next((j for j, old in enumerate(row) if old > value), len(row))
            if pos == len(row):
                row.append(value)
                recording[r].append(label)
                break
            row[pos], value = value, row[pos]
        else:
            insertion.append([value])
            recording.append([label])
    return insertion, recording


def saturation_check(m: int) -> dict[str, Any]:
    """Finite standard-tableau saturation; does not test semistandard RSK.

    Additionally verifies every group contains exactly f^alpha f^beta
    initial fillings, using independent Young-removal dimensions.
    """
    groups: dict[tuple[Any, ...], list[int | bool]] = {}
    records = 0
    for word in permutations(range(1, m + 1)):
        insertion, recording = row_insert(word)
        if len(insertion) > 4:
            continue
        for P in range(1, m):
            alpha = tuple(sum(x <= P for x in row) for row in recording)
            alpha = tuple(x for x in alpha if x)
            if len(alpha) > 2:
                continue
            jkey = tuple(tuple(x if x > P else 0 for x in row) for row in recording)
            for Q in range(1, m - P + 1):
                beta = tuple(sum(x <= Q for x in row) for row in insertion)
                beta = tuple(x for x in beta if x)
                if len(beta) > 2:
                    continue
                ikey = tuple(tuple(x if x > Q else 0 for x in row) for row in insertion)
                key = (P, Q, ikey, jkey)
                empty = not any(value <= Q for value in word[:P])
                complete = skew_young_removal(alpha, ()) * skew_young_removal(beta, ())
                if key in groups:
                    group = groups[key]
                    require(group[0] == empty and group[2] == complete,
                            f"Saturation fails at m={m}, P={P}, Q={Q}")
                    group[1] += 1
                else:
                    groups[key] = [empty, 1, complete]
                records += 1
    for group in groups.values():
        require(group[1] == group[2], f"Incomplete initial-filling group at m={m}")
    return dict(m=m, tableau_boundary_records=records, outer_skew_groups=len(groups),
                multiple_initial_filling_groups=sum(group[1] > 1 for group in groups.values()),
                complete_filling_groups=len(groups), status="PASS")


def direct_unique_count(n: int) -> dict[str, Any]:
    """Count increasing five-subsequences by ending position, capped at two."""
    unique = 0
    for word in permutations(range(n)):
        dp: list[list[int]] = []
        count = 0
        for i, value in enumerate(word):
            row = [0, 1, 0, 0, 0, 0]
            for length in range(2, 6):
                row[length] = min(2, sum(dp[j][length - 1]
                                         for j in range(i) if word[j] < value))
            dp.append(row)
            count = min(2, count + row[5])
        unique += count == 1
    return dict(n=n, permutations=factorial(n), unique=unique, status="PASS")


def avoidance_recurrence(n_max: int) -> list[int]:
    """OEIS A047889's order-two recurrence, separate from tableau enumeration."""
    values = [1, 1]
    for n in range(n_max - 1):
        top = ((20*n**3 + 182*n**2 + 510*n + 428) * values[-1]
               - (64*n**3 + 256*n**2 + 320*n + 128) * values[-2])
        bottom = n**3 + 16*n**2 + 85*n + 150
        value, remainder = divmod(top, bottom)
        require(remainder == 0 and value > 0, f"Avoidance recurrence invalid at n={n}")
        values.append(value)
    return values[:n_max + 1]


def boundary_vector(P: int, R: int, Q: int, T: int) -> Boundary:
    return (P - R, R - 1, T - 1, Q - T)


def glue(halves: list[dict[Boundary, int]], extra: int) -> int:
    """Exact four-binomial convolution; exploit only the proved K symmetry."""
    binomial = [[comb(a + b, a) for b in range(extra + 1)] for a in range(extra + 1)]
    total = 0
    for s in range(extra // 2 + 1):
        t = extra - s
        subtotal = 0
        for (a, b, c, d), h in halves[s].items():
            A, B, C, D = binomial[a], binomial[b], binomial[c], binomial[d]
            subtotal += h * sum(k * A[g] * B[j] * C[e] * D[f]
                               for (e, f, g, j), k in halves[t].items())
        total += subtotal if s == t else 2 * subtotal
    return total


def schur_dimension4(shape: Partition) -> int:
    padded = shape + (0,) * (4 - len(shape))
    value = Fraction(1)
    for i in range(4):
        for j in range(i + 1, 4):
            value *= Fraction(padded[i] - padded[j] + j - i, j - i)
    require(value.denominator == 1, "Nonintegral Weyl dimension")
    return value.numerator


def leading_terms(v: Boundary) -> list[Fraction]:
    a, b, c, d = v
    P, R, Q, T = a + b + 1, b + 1, c + d + 1, c + 1
    scale = Fraction(256, 4**(P + Q))
    terms = []
    for tau in TAUS:
        left = sum(coeff * schur_dimension4(nu) for nu, coeff in gl2_adjoint(P, R, tau))
        right = sum(coeff * schur_dimension4(nu) for nu, coeff in gl2_adjoint(Q, T, transpose(tau)))
        terms.append(scale * (-1)**sum(tau) * left * right)
    return terms


def polynomial_product(a: dict[tuple[int, ...], int],
                       b: dict[tuple[int, ...], int]) -> dict[tuple[int, ...], int]:
    out: dict[tuple[int, ...], int] = defaultdict(int)
    for x, u in a.items():
        for y, v in b.items():
            out[tuple(i + j for i, j in zip(x, y))] += u * v
    return {key: value for key, value in out.items() if value}


def schur2_monomials(shape: Partition) -> dict[tuple[int, int], int]:
    a, b = (shape + (0, 0))[:2]
    return {(a - i, b + i): 1 for i in range(a - b + 1)}


def algebra_checks() -> tuple[dict[str, Any], dict[str, Any]]:
    gl2_tests = 0
    for n in range(13):
        for nu in partitions(n, 2):
            for tau in TAUS:
                left = polynomial_product(schur2_monomials(nu), schur2_monomials(tau))
                right: dict[tuple[int, ...], int] = defaultdict(int)
                for alpha in gl2_product(nu, tau):
                    for exponent, coefficient in schur2_monomials(alpha).items():
                        right[exponent] += coefficient
                require(left == right, f"GL(2) identity fails for {nu}, {tau}")
                gl2_tests += 1
    product = {(0, 0, 0, 0): 1}
    for i in range(2):
        for j in range(2):
            exponent = [0, 0, 0, 0]
            exponent[i] = exponent[j + 2] = 1
            product = polynomial_product(product, {(0, 0, 0, 0): 1, tuple(exponent): -1})
    expansion: dict[tuple[int, ...], int] = defaultdict(int)
    for tau in TAUS:
        for a, ca in schur2_monomials(tau).items():
            for b, cb in schur2_monomials(transpose(tau)).items():
                expansion[a + b] += (-1)**sum(tau) * ca * cb
    expansion = {key: value for key, value in expansion.items() if value}
    require(product == expansion, "Six-term dual-Cauchy polynomial mismatch")
    shift_tests = 0
    for P in range(1, 21):
        for Q in range(1, 22 - P):
            for tau in TAUS:
                k = sum(tau)
                if k <= min(P, Q):
                    lhs = Fraction(16)**(2 - k) * Fraction(4)**(-P - Q + 2*k)
                    require(lhs == Fraction(256, 4**(P + Q)), "Leading normalization shift mismatch")
                    shift_tests += 1
    regev = Fraction(4**8 * factorial(1) * factorial(2) * factorial(3), 2**9)
    require(regev == 1536, "Regev four-row normalization mismatch")
    h0_terms = leading_terms((0, 0, 0, 0))
    require(sum(h0_terms) == 240, "h(0) normalization mismatch")
    normalization = dict(dual_cauchy_monomials=len(product), dual_cauchy_status="PASS",
                         shift_identity_tests=shift_tests, regev_rational_factor=str(regev),
                         h0_signed_terms=[str(value) for value in h0_terms if value],
                         zero_boundary_tests=20, status="PASS")
    return dict(nu_size_max=12, tests=gl2_tests, status="PASS"), normalization


def source_array(values: Sequence[int], label: str) -> list[int]:
    require(isinstance(values, (list, tuple)), f"{label} must be a plain list or tuple")
    require(len(values) >= 25, f"{label} must include n=0 through n=24")
    require(all(type(value) is int and value >= 0 for value in values),
            f"{label} contains a nonnegative-integer data error")
    return list(values[:25])


def run(source_unique: Sequence[int], source_avoidance: Sequence[int]) -> dict[str, Any]:
    """Replay all supported finite checks; raise ReplayError on any discrepancy.

    The return value is deterministic and JSON-friendly. No elapsed time,
    paths, timestamps, floating-point estimates, or numeric estimate of R5
    enter the result. Published inputs are used only for final comparisons.
    """
    expected_u = source_array(source_unique, "source_unique")
    expected_a = source_array(source_avoidance, "source_avoidance")
    require(expected_u[:5] == [0] * 5, "Unique source has invalid n<5 initial values")
    determinant_tests = 0
    for n in range(11):
        for outer in partitions(n):
            for k in range(n + 1):
                for inner in partitions(k):
                    require(skew_determinant(outer, inner) == skew_young_removal(outer, inner),
                            f"Skew determinant mismatch for {outer}/{inner}")
                    determinant_tests += 1
    gl2, normalization = algebra_checks()
    rsk = [sum(skew_determinant(shape, ())**2 for shape in partitions(n)) for n in range(25)]
    recurrence = avoidance_recurrence(24)
    require(rsk == recurrence == expected_a, "Avoidance RSK/recurrence/source mismatch")
    halves: list[dict[Boundary, int]] = []
    boundary_results = []
    gluing_results = []
    for extra in range(20):
        m = extra + 2
        table = six_term_table(m)
        if m <= 8:
            boundary_results.append(boundary_enumeration(m, table))
        half = {boundary_vector(*key): value for key, value in table.items() if value}
        halves.append(half)
        zero = half.get((0, 0, 0, 0), 0)
        require(zero == rsk[extra + 2] - rsk[extra + 1], f"H_s(0) fails at s={extra}")
        unique = glue(halves, extra)
        n = extra + 5
        require(unique == expected_u[n], f"Unique source/gluing mismatch at n={n}")
        gluing_results.append(dict(n=n, unique=unique, half_states=len(half),
                                   half_mass=sum(half.values()), zero_boundary=zero,
                                   source_match=True, status="PASS"))
    direct_results = [direct_unique_count(n) for n in range(5, 9)]
    for row in direct_results:
        require(row["unique"] == expected_u[row["n"]], "Direct unique enumeration mismatch")
    saturation_results = [saturation_check(m) for m in (6, 7, 8)]
    leading_values = []
    for P, R, Q, T in boundary_parameters(6):
        v = boundary_vector(P, R, Q, T)
        value = sum(leading_terms(v), Fraction(0))
        require(value >= 0, f"Negative leading h value at {v}")
        leading_values.append(dict(v=list(v), h=str(value)))
    leading_values.sort(key=lambda row: (sum(row["v"]), row["v"]))
    lower_bound = 2 * Fraction(1, 16**5) * sum(leading_terms((0, 0, 0, 0)))
    require(lower_bound == Fraction(15, 32768), "R5 lower bound mismatch")
    return dict(schema="report138-exact-replay-v1",
                determinant_crosscheck=dict(outer_size_max=10, rows_max=4,
                                            tests=determinant_tests, status="PASS"),
                gl2_crosscheck=gl2,
                avoidance=dict(n_max=24, rsk=rsk, recurrence=recurrence,
                               source_match=True, status="PASS"),
                boundary_enumeration=boundary_results, saturation=saturation_results,
                direct_unique=direct_results, gluing=gluing_results,
                leading=dict(values=leading_values, h0="240", R5_lower_bound=str(lower_bound), status="PASS"),
                normalization=normalization, status="PASS")
