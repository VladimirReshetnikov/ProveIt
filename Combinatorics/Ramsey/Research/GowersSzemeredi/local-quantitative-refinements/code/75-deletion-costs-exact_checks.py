#!/usr/bin/env python3
"""Bounded, exact regression checks for Report287; never a theorem prover.

Only the Python standard library is used. Public inputs are deliberately small,
strictly typed, and checked before enumeration. All arithmetic is integral or
rational. The actual doubly exponential theorem exponent is never constructed.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from itertools import product
import json

MAX_N = 16
MAX_CERTIFICATE_N = 64
MAX_BITS = 128
MAX_WORD_N = 6
MAX_WORDS = 50000
MAX_MODEL_POINTS = 8
FINITE_EXPONENTS = (8, 16, 32)


def require(condition, message):
    """An always-live gate, including under python -O."""
    if type(condition) is not bool or not condition:
        raise RuntimeError(message)


def integer(value, name, lower, upper):
    if type(value) is not int or not lower <= value <= upper:
        raise ValueError(name + ' must be an integer in the permitted finite range')
    return value


def rational(value):
    if type(value) not in (int, Q):
        raise ValueError('an exact int or Fraction is required; bools are not integers here')
    if type(value) is int:
        if value.bit_length() > MAX_BITS:
            raise ValueError('rational bit limit exceeded')
        value = Q(value)
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise ValueError('rational bit limit exceeded')
    return value


def ceil_fraction(value):
    value = rational(value)
    return -(-value.numerator // value.denominator)


def _ceil(value):
    # Internal arithmetic may produce larger rationals from bounded inputs.
    return -(-value.numerator // value.denominator)


def sequence(value, length, name):
    if type(value) not in (list, tuple) or len(value) != length:
        raise ValueError(name + ' must be a bounded list or tuple of the stated length')
    return tuple(value)


def modulus(N):
    return integer(N, 'N', 1, MAX_N)


def word(N, values):
    modulus(N)
    return tuple(integer(v, 'residue', 0, N - 1) for v in sequence(values, N, 'word'))


def weight(N, weights):
    modulus(N)
    result = tuple(rational(v) for v in sequence(weights, N, 'weight'))
    if any(v < 0 for v in result):
        raise ValueError('weights must be nonnegative')
    return result


def subset(size, values, name, nonempty=False):
    integer(size, 'universe size', 1, MAX_N)
    if type(nonempty) is not bool:
        raise ValueError('nonempty must be bool')
    if type(values) not in (list, tuple) or len(values) > size:
        raise ValueError(name + ' must be a bounded list or tuple')
    result = tuple(integer(v, name + ' point', 0, size - 1) for v in values)
    if len(set(result)) != len(result) or (nonempty and not result):
        raise ValueError(name + ' must have distinct points and satisfy nonemptiness')
    return result


def _convolution(N, left, right):
    result = [Q(0)] * N
    for x in range(N):
        for y in range(N):
            result[(x + y) % N] += left[x] * right[y]
    return tuple(result)


def convolution(N, left, right):
    modulus(N)
    return _convolution(N, weight(N, left), weight(N, right))


def _graph_energy(N, values, weights):
    buckets = {}
    for x in range(N):
        for y in range(N):
            key = ((x + y) % N, (values[x] + values[y]) % N)
            buckets[key] = buckets.get(key, Q(0)) + weights[x] * weights[y]
    return sum((v * v for v in buckets.values()), Q(0))


def additive_energy(N, weights):
    modulus(N)
    weights = weight(N, weights)
    return sum((v * v for v in _convolution(N, weights, weights)), Q(0))


def respected_energy(N, values, weights):
    values = word(N, values)
    return _graph_energy(N, values, weight(N, weights))


def energy_ratio(N, values, weights):
    values = word(N, values)
    weights = weight(N, weights)
    if not any(weights):
        raise ValueError('relative energy requires a nonzero weight')
    denominator = sum((v * v for v in _convolution(N, weights, weights)), Q(0))
    require(denominator > 0, 'nonzero nonnegative weights have positive energy')
    return _graph_energy(N, values, weights) / denominator


def full_group_energy(N, values):
    """Independent difference-histogram formula using integers."""
    values = word(N, values)
    histograms = []
    for h in range(N):
        counts = [0] * N
        for x in range(N):
            counts[(values[(x + h) % N] - values[x]) % N] += 1
        histograms.append(tuple(counts))
    Qh = tuple(sum(c * c for c in counts) for counts in histograms)
    return {'energy': sum(Qh), 'Qh': Qh, 'histograms': tuple(histograms)}


def affine_parameters(N, values):
    values = word(N, values)
    beta = values[0]
    for alpha in range(N):
        if all(values[x] == (alpha * x + beta) % N for x in range(N)):
            return (alpha, beta)
    return None


def parity_parameters(N, values):
    """Return a parity representation for even N; return None otherwise."""
    values = word(N, values)
    if N % 2:
        return None
    beta = values[0]
    for alpha in range(N):
        delta = (values[1] - beta - alpha) % N
        if all(values[x] == (alpha * x + beta + delta * (x % 2)) % N for x in range(N)):
            return (alpha, beta, delta)
    return None


def best_affine_agreement(N, values):
    values = word(N, values)
    return max(sum(values[x] == (alpha * x + beta) % N for x in range(N))
               for alpha in range(N) for beta in range(N))


def four_window_certificate(N, values):
    """Four local image values; no complete word or large group is allocated."""
    integer(N, 'N', 7, MAX_CERTIFICATE_N)
    values = tuple(integer(v, 'residue', 0, N - 1)
                   for v in sequence(values, 4, 'four images'))
    ordinary = {}; graph = {}
    for i in range(4):
        for j in range(4):
            s = (i + j) % N
            ordinary[s] = ordinary.get(s, 0) + 1
            key = (s, (values[i] + values[j]) % N)
            graph[key] = graph.get(key, 0) + 1
    denominator = sum(v * v for v in ordinary.values())
    numerator = sum(v * v for v in graph.values())
    A = (values[0] + values[2] - 2 * values[1]) % N
    B = (values[1] + values[3] - 2 * values[2]) % N
    M = (values[0] + values[3] - values[1] - values[2]) % N
    require(denominator == 44, 'four-window denominator must be 44')
    require(M == (A + B) % N, 'four-window defect identity')
    if M:
        require(bool(A or B), 'nonzero M forces A or B nonzero')
        require(numerator <= 32, 'four-window 8/11 implication')
    return {'A': A, 'B': B, 'M': M, 'additive': denominator,
            'respected': numerator, 'ratio': Q(numerator, denominator)}



def relative_energy_certificate(N, values):
    """Linear-arithmetic-operation certificate scan for bounded N<=64.

General maps receive an upper bound witnessed by an indicator weight, never an
assertion that this is the exact infimum. Only the affine/parity branches return
exact_r, invoking the proved all-weight identities. For N<=6 a constant-sized
full-group pair enumeration is used when the middle relation fails.
"""
    integer(N, 'certificate modulus', 1, MAX_CERTIFICATE_N)
    values = tuple(integer(v, 'certificate residue', 0, N - 1)
                   for v in sequence(values, N, 'certificate word'))
    relation_checks = 0
    failure = None
    for x in range(N):
        relation_checks += 1
        if (values[x] + values[(x + 3) % N] - values[(x + 1) % N]
                - values[(x + 2) % N]) % N:
            failure = x
            break
    if failure is not None:
        if N >= 7:
            support = tuple((failure + j) % N for j in range(4))
            row = four_window_certificate(N, tuple(values[x] for x in support))
            numerator = row['respected']; denominator = row['additive']
        else:
            support = tuple(range(N)); buckets = {}
            for x in range(N):
                for y in range(N):
                    key = ((x + y) % N, (values[x] + values[y]) % N)
                    buckets[key] = buckets.get(key, 0) + 1
            numerator = sum(count * count for count in buckets.values())
            denominator = N ** 3
        bound = Q(numerator, denominator)
        require(bound <= Q(8, 11), 'indicator certificate bound')
        return {'kind': 'upper_bound', 'exact_r': None, 'upper_bound': bound,
                'indicator_support': support, 'respected': numerator,
                'additive': denominator, 'failed_window_start': failure,
                'relation_checks': relation_checks, 'representation': None}
    beta = values[0]
    if N == 1:
        alpha = 0; delta = 0
    else:
        d0 = (values[1] - values[0]) % N
        if N % 2:
            alpha = d0; delta = 0
        else:
            d1 = (values[2 % N] - values[1]) % N
            t = (d0 + d1) % N
            require(t % 2 == 0, 'even cyclic closure permits solving 2 alpha=t')
            alpha = t // 2
            delta = (d0 - alpha) % N
    require(all(values[x] == (alpha * x + beta + delta * (x % 2)) % N for x in range(N)),
            'recovered affine/parity representation')
    if (2 * delta) % N == 0:
        if N > 1:
            alpha = (values[1] - values[0]) % N
        require(all(values[x] == (alpha * x + beta) % N for x in range(N)),
                'canonical affine representation')
        kind = 'affine'; exact = Q(1); representation = (alpha, beta)
    else:
        require(N % 2 == 0, 'non-affine parity requires even modulus')
        kind = 'parity'; exact = Q(3, 4); representation = (alpha, beta, delta)
    numerator = exact * N ** 3
    require(numerator.denominator == 1, 'full-weight witness energy is integral')
    return {'kind': kind, 'exact_r': exact, 'upper_bound': exact,
            'indicator_support': tuple(range(N)), 'respected': numerator.numerator,
            'additive': N ** 3, 'failed_window_start': None,
            'relation_checks': relation_checks, 'representation': representation}


def parity_identity(N, alpha, beta, delta, weights):
    modulus(N)
    if N % 2:
        raise ValueError('parity identity requires an even modulus')
    for value in (alpha, beta, delta):
        integer(value, 'parity parameter', 0, N - 1)
    if (2 * delta) % N == 0:
        raise ValueError('the non-affine parity identity requires 2 delta nonzero')
    weights = weight(N, weights)
    values = tuple((alpha * x + beta + delta * (x % 2)) % N for x in range(N))
    e = tuple(weights[x] if x % 2 == 0 else Q(0) for x in range(N))
    o = tuple(weights[x] if x % 2 else Q(0) for x in range(N))
    ee = _convolution(N, e, e); oo = _convolution(N, o, o); eo = _convolution(N, e, o)
    U = sum((v * v for v in ee), Q(0)); V = sum((v * v for v in oo), Q(0))
    C = sum((ee[x] * oo[x] for x in range(N)), Q(0))
    D = sum((v * v for v in eo), Q(0))
    R = tuple(sum((e[x] * o[(x + h) % N] for x in range(N)), Q(0)) for h in range(N))
    require(C == sum((R[h] * R[-h % N] for h in range(N)), Q(0)), 'parity C correlation')
    require(D == sum((v * v for v in R), Q(0)), 'parity D correlation')
    add = additive_energy(N, weights); respected = _graph_energy(N, values, weights)
    require(add == U + V + 2 * C + 4 * D, 'parity additive splitting')
    require(respected == U + V + 4 * D, 'parity respected splitting')
    norm_term = sum(((ee[x] - oo[x]) ** 2 for x in range(N)), Q(0)) / 4
    correlation_term = sum(((R[h] - R[-h % N]) ** 2 for h in range(N)), Q(0)) / 2
    gap = respected - Q(3, 4) * add
    require(gap == norm_term + correlation_term, 'exact parity sum of squares')
    require(gap >= 0, 'parity 3/4 lower bound')
    return {'additive': add, 'respected': respected, 'gap': gap,
            'norm_square_term': norm_term, 'correlation_square_term': correlation_term,
            'U': U, 'V': V, 'C': C, 'D': D}


def graph_convolution_certificate(N, values, weights, support, alphabet, root_upper):
    """Check disjoint graph-convolution masses and a rational Holder bound.

root_upper is any positive rational t with t^3 >= M/N. All comparisons are
cross-multiplied, so this routine need not approximate an irrational cube root.
"""
    values = word(N, values); weights = weight(N, weights)
    support = subset(N, support, 'support', nonempty=True)
    alphabet = subset(N, alphabet, 'alphabet', nonempty=True)
    J = set(support); S = set(alphabet)
    if any(values[x] != 0 for x in range(N) if x not in J):
        raise ValueError('word must vanish outside the declared support')
    if any(values[x] not in S for x in J):
        raise ValueError('inside image must lie in the declared alphabet')
    t = rational(root_upper)
    if t <= 0:
        raise ValueError('positive rational root upper bound required')
    JJ = {(x + y) % N for x in J for y in J}
    SS = {(x + y) % N for x in S for y in S}
    M = len(JJ) * len(SS)
    if N * t ** 3 < M:
        raise ValueError('root upper bound does not satisfy N t^3 >= M')
    inside = tuple(weights[x] if x in J else Q(0) for x in range(N))
    outside = tuple(weights[x] if x not in J else Q(0) for x in range(N))
    A = sum(outside, Q(0)); B = sum(inside, Q(0))
    inner_energy = _graph_energy(N, values, inside)
    outer_energy = _graph_energy(N, values, outside)
    energy = _graph_energy(N, values, weights)
    require(N * outer_energy >= A ** 4, 'outside convolution Cauchy-Schwarz')
    require(M * inner_energy >= B ** 4, 'inside graph-convolution Cauchy-Schwarz')
    require(energy >= outer_energy + inner_energy, 'inside/outside disjoint families')
    mass_numerator = M * A ** 4 + N * B ** 4
    require(N * M * energy >= mass_numerator, 'two-mass energy lower bound')
    require(mass_numerator * (1 + t) ** 3 >= M * (A + B) ** 4,
            'rational root-free Holder comparison')
    interval_cap = (2 * len(J) - 1) * (2 * len(S) - 1)
    intervals = J == set(range(len(J))) and S == set(range(len(S)))
    if intervals:
        require(M <= interval_cap < 4 * len(J) * len(S), 'interval sumset bound')
    return {'energy': energy, 'outside_energy': outer_energy, 'inside_energy': inner_energy,
            'A': A, 'B': B, 'M': M, 'sumset_sizes': (len(JJ), len(SS)),
            'two_mass_lower': mass_numerator / (N * M),
            'rational_holder_lower': (A + B) ** 4 / (N * (1 + t) ** 3),
            'root_upper': t, 'intervals': intervals, 'interval_cap': interval_cap}


def deletion_certificate(size, retained, covered, kept, rho):
    """Finite set model of H intersect D subset C, counting deleted points."""
    integer(size, 'model size', 1, MAX_MODEL_POINTS)
    D = set(subset(size, retained, 'retained'))
    C = set(subset(size, covered, 'covered'))
    H = set(subset(size, kept, 'kept'))
    rho = rational(rho)
    if not 0 < rho < 1:
        raise ValueError('model loss must be strictly between zero and one')
    if len(H) < (1 - rho) * size:
        raise ValueError('kept set violates the local density premise')
    if not H.intersection(D).issubset(C):
        raise ValueError('kept retained points must be covered')
    deleted = size - len(D)
    lower = max(Q(0), (1 - rho) * size - len(C))
    require(len(H) <= deleted + len(C), 'deleted points contribute freely to H')
    require(deleted >= lower, 'arbitrary retained-domain deletion count')
    return {'deleted': deleted, 'covered': len(C), 'kept': len(H),
            'kept_deleted': len(H - D), 'kept_retained': len(H & D),
            'lower_deleted': lower}


def finite_surrogate(E, cube_root_gamma):
    """Finite-exponent arithmetic only: E in {8,16,32}, gamma=u^3.

The restriction gamma=u^3 keeps eta=(gamma^(-8/3)-1)^3 exactly rational.
These are algebraic regressions, not constructions at the actual theorem E.
"""
    integer(E, 'finite regression exponent', 8, 32)
    if E not in FINITE_EXPONENTS:
        raise ValueError('only the documented finite surrogate exponents are accepted')
    u = rational(cube_root_gamma)
    if not 0 < u < 1 or max(u.numerator.bit_length(), u.denominator.bit_length()) > 8:
        raise ValueError('cube root of gamma must be in (0,1), with at most 8-bit numerator/denominator')
    gamma = u ** 3; eta = (u ** -8 - 1) ** 3
    rho = Q(E, E + 2); q = (gamma * rho) ** -E
    R_cont = Q(5, 4) * (E + 2) * q
    R = _ceil(R_cont); T = (E + 2) * q
    beta = 1 - rho - Q(5, 4) * q / R
    lam = eta / (4 * R)
    require(beta >= Q(1, E + 2), 'rounded optimized deletion coefficient')
    require(0 < lam < Q(1, 2), 'finite E>=8 density bound')
    require(R_cont <= R < R_cont + 1, 'exact ceiling')
    require(R <= Q(3, 2) * T, 'rounded alphabet upper bound')
    require(q < 8 * gamma ** -E, 'elementary rational upper bound for (1+2/E)^E')
    Q0 = (2 / gamma) ** E
    require(R <= Q0 ** 2, 'image-budget regression')
    continuous = eta * gamma ** E * E ** E / (5 * (E + 2) ** (E + 2))
    def objective(alphabet_size):
        return eta / 4 * ((1 - rho) / alphabet_size - Q(5, 4) * q / alphabet_size ** 2)
    require(objective(R_cont) == continuous, 'continuous surrogate value')
    for candidate in (R_cont / 2, R_cont, 2 * R_cont, Q(R)):
        square_gap = 5 * eta * q / 16 * (1 / candidate - 1 / R_cont) ** 2
        require(continuous - objective(candidate) == square_gap,
                'fixed-loss alphabet optimization exact square')
    require(E / rho - 2 / (1 - rho) == 0, 'loss optimizer derivative')
    for j in range(1, 20):
        trial = Q(j, 20)
        require(trial ** E * (1 - trial) ** 2 <= rho ** E * (1 - rho) ** 2,
                'finite loss-grid regression')
    N = _ceil(10 / lam)
    m = (lam * N).numerator // (lam * N).denominator
    require(Q(m, N) >= lam / 2, 'floor density lower bound')
    lower = Q(m, N * (E + 2))
    rounded_constant = eta / (8 * R * (E + 2))
    sharper = eta / (4 * R * (E + 2)) - Q(1, N * (E + 2))
    require(lower >= rounded_constant and lower >= sharper, 'finite rounded deletion bounds')
    rational_constant = eta * gamma ** E / (96 * (E + 2) ** 2)
    require(rounded_constant >= rational_constant, 'weaker rational substitute for the e^2 comparison')
    baseline_R = _ceil(4 * Q0)
    half_beta = Q(1, 2) - Q(5, 4) * Q0 / baseline_R
    require(half_beta >= Q(3, 16), 'original-alphabet half-loss bound')
    three_fifths_beta = Q(2, 5) - Q(5, 4) * (gamma * Q(3, 5)) ** -E / baseline_R
    if E >= 16:
        require(three_fifths_beta > Q(3, 8), 'improved original-alphabet bound for E>=16')
    return {'E': E, 'gamma': gamma, 'eta': eta, 'rho': rho, 'q': q, 'R': R,
            'beta': beta, 'lambda': lam, 'continuous_surrogate': continuous,
            'rounded_surrogate': objective(Q(R)), 'sample_N': N, 'sample_m': m,
            'rounded_lower': lower, 'positive_constant': rounded_constant,
            'sharper_lower': sharper, 'weaker_rational_constant': rational_constant,
            'half_beta': half_beta, 'three_fifths_beta': three_fifths_beta}


def classify_small_words(N, normalized=False):
    integer(N, 'small modulus', 1, MAX_WORD_N)
    if type(normalized) is not bool:
        raise ValueError('normalized must be bool')
    exponent = N - 1 if normalized else N
    total = N ** exponent
    if total > MAX_WORDS:
        raise ValueError('word-space limit exceeded')
    affine = 0; parity = 0; other = 0; max_other_energy = 0
    cases = product(range(N), repeat=exponent)
    for raw in cases:
        values = (0,) + raw if normalized else raw
        a = affine_parameters(N, values)
        p = parity_parameters(N, values)
        row = full_group_energy(N, values)
        energy = row['energy']
        for h, counts in enumerate(row['histograms']):
            require(sum(v * counts[v] for v in range(N)) % N == 0, 'increment sum zero')
            require(row['Qh'][h] == row['Qh'][-h % N], 'increment h/-h symmetry')
            if max(counts) < N:
                require(max(counts) != N - 1, 'nonconstant increment cannot have N-1 plus 1')
                if N >= 4:
                    require(row['Qh'][h] <= (N - 2) ** 2 + 4, 'nonconstant histogram bound')
        if a is not None:
            affine += 1
            require(energy == N ** 3, 'affine full-group energy')
        elif p is not None:
            parity += 1
            require((2 * p[2]) % N != 0, 'non-affine parity parameter')
            require(4 * energy == 3 * N ** 3, 'non-affine parity full-group energy')
        else:
            other += 1; max_other_energy = max(max_other_energy, energy)
            require(11 * energy <= 8 * N ** 3, 'small-modulus classification upper bound')
            if N == 3:
                require(energy == 15, 'N=3 non-affine histogram energy')
            elif N == 4:
                require(energy <= 40, 'N=4 nonparity bound')
            elif N == 5:
                require(energy <= 77, 'N=5 non-affine bound')
            elif N == 6:
                require(energy <= 152, 'N=6 nonparity bound')
    require(affine + parity + other == total, 'small-word inventory')
    return {'N': N, 'normalized_a0_zero': normalized, 'words': total,
            'affine': affine, 'nonaffine_parity': parity, 'other': other,
            'max_other_full_weight_energy': max_other_energy}


def check_four_windows():
    tested = 0; defective = 0; worst = 0
    for N in (7, 8):
        for values in product(range(N), repeat=4):
            row = four_window_certificate(N, values)
            tested += 1
            if row['M']:
                defective += 1; worst = max(worst, row['respected'])
    return {'windows': tested, 'nonzero_M_windows': defective, 'max_defective_energy': worst,
            'denominator': 44}


def check_parity():
    cases = 0; equality = 0
    for N in (4, 6, 8, 10, 12, 16):
        for delta in range(1, N):
            if (2 * delta) % N == 0:
                continue
            alpha = 1; beta = 2
            values = tuple((alpha * x + beta + delta * (x % 2)) % N for x in range(N))
            require(best_affine_agreement(N, values) <= N // 2, 'non-affine parity affine-agreement cap')
            for weights in ((1,) * N, tuple(Q(x + 1, x + 2) for x in range(N)),
                            tuple(Q((x * x + 1) % 5, 3) for x in range(N))):
                row = parity_identity(N, alpha, beta, delta, weights); cases += 1
                if weights == (1,) * N:
                    require(row['gap'] == 0, 'parity endpoint is attained by full weight')
                    equality += 1
    return {'identities': cases, 'full_weight_equalities': equality, 'affine_agreement_checked': equality}


def check_graph_convolution():
    cases = 0
    examples = ((8, (0, 1, 1, 0, 0, 0, 0, 0), (0, 1, 2), (0, 1), 2),
                (9, (1, 0, 0, 2, 0, 0, 0, 0, 0), (0, 3), (1, 2), 2),
                (8, (0,) * 8, (0,), (0,), Q(1, 2)),
                (4, (1, 1, 1, 1), (0, 1, 2, 3), (1,), 1))
    for N, values, J, S, t in examples:
        for weights in ((0,) * N, (1,) * N, tuple(Q(x + 1, x + 2) for x in range(N))):
            graph_convolution_certificate(N, values, weights, J, S, t); cases += 1
    # A sharp algebraic Holder instance, without claiming sharpness for a word.
    N = 8; M = 1; A = Q(2); B = Q(1); t = Q(1, 2)
    require((M * A ** 4 + N * B ** 4) * (1 + t) ** 3 == M * (A + B) ** 4,
            'algebraic Holder equality at A:B=N^(1/3):M^(1/3)')
    return {'mass_certificates': cases, 'holder_equality': True}


def check_deletion_model():
    size = 5; rho = Q(1, 5); cases = 0; free_deleted_cases = 0
    sets = tuple(tuple(x for x in range(size) if mask & (1 << x)) for mask in range(1 << size))
    for D, C, H in product(sets, repeat=3):
        if len(H) < 4 or not set(H).intersection(D).issubset(C):
            continue
        row = deletion_certificate(size, D, C, H, rho); cases += 1
        free_deleted_cases += row['kept_deleted'] > 0
    witness = deletion_certificate(5, (0, 2), (0,), (0, 1, 3, 4), rho)
    require(witness['deleted'] == witness['lower_deleted'] == 3, 'sharp finite deletion model')
    require(witness['kept_deleted'] == 3, 'deleted points must be counted in H')
    return {'admissible_triples': cases, 'triples_with_kept_deleted_points': free_deleted_cases,
            'equality_witness': witness}


def check_sparse_witness():
    N = 8; values = (0, 0, 0, 1, 0, 0, 0, 0)
    weights = (1, 1, 1, 1, 0, 0, 0, 0)
    ratio = energy_ratio(N, values, weights)
    require(ratio == Q(8, 11), 'explicit one-point sparse defect witness')
    require(affine_parameters(N, values) is None and parity_parameters(N, values) is None,
            'sparse witness is neither affine nor parity')
    require(best_affine_agreement(N, values) == 7, 'sparse witness agrees with zero on seven points')
    return {'N': N, 'defect_support': (3,), 'weight_support': (0, 1, 2, 3),
            'additive': additive_energy(N, weights), 'respected': respected_energy(N, values, weights),
            'ratio': ratio, 'best_affine_agreement': 7}



def _target_word(N, values, target_modulus):
    modulus(N)
    if target_modulus is not None:
        integer(target_modulus, 'target modulus', 1, 32)
    values = sequence(values, N, 'abelian-target word')
    low, high = (-256, 256) if target_modulus is None else (0, target_modulus - 1)
    return tuple(integer(v, 'target value', low, high) for v in values)


def _target_reduce(value, target_modulus):
    return value if target_modulus is None else value % target_modulus


def target_respected_energy(N, values, weights, target_modulus=None):
    """Finite examples in Z or Z/MZ; no general abstract-group interface."""
    values = _target_word(N, values, target_modulus)
    weights = weight(N, weights); buckets = {}
    for x in range(N):
        for y in range(N):
            key = ((x + y) % N, _target_reduce(values[x] + values[y], target_modulus))
            buckets[key] = buckets.get(key, Q(0)) + weights[x] * weights[y]
    return sum((v * v for v in buckets.values()), Q(0))


def abelian_small_certificate(N, values, target_modulus=None):
    """Uniform-weight small-N checks for the separate arbitrary-target theorem.

Only integer and finite cyclic target examples are implemented. This routine
does not assert the same-target 8/11 classification for arbitrary targets.
"""
    integer(N, 'small abelian domain', 1, 6)
    values = _target_word(N, values, target_modulus)
    histograms = []; derivatives = []
    for h in range(N):
        diff = tuple(_target_reduce(values[(x + h) % N] - values[x], target_modulus)
                     for x in range(N))
        counts = {}
        for v in diff:
            counts[v] = counts.get(v, 0) + 1
        derivatives.append(diff); histograms.append(counts)
    Qh = tuple(sum(v * v for v in counts.values()) for counts in histograms)
    energy = sum(Qh)
    require(all(Qh[h] == Qh[-h % N] for h in range(N)), 'arbitrary-target histogram symmetry')
    affine = len(histograms[1 % N]) == 1
    even_form = N % 2 == 0 and len(histograms[2 % N]) == 1
    representation = None
    if affine:
        u = derivatives[1 % N][0]
        require(_target_reduce(N * u, target_modulus) == 0, 'affine slope respects cyclic closure')
        require(all(_target_reduce(values[0] + x * u, target_modulus) == values[x] for x in range(N)),
                'arbitrary-target affine representation')
        kind = 'affine'; exact = Q(1); bound = Q(1)
        representation = (values[0], u)
        require(energy == N ** 3, 'arbitrary-target affine energy')
    elif even_form:
        beta = values[0]; u = derivatives[1][0]; d = derivatives[2 % N][0]
        require(_target_reduce((N // 2) * d, target_modulus) == 0, 'division-free even closure')
        require(_target_reduce(d - 2 * u, target_modulus) != 0, 'non-affine even defect')
        require(all(_target_reduce(beta + (x // 2) * d + (x % 2) * u, target_modulus) == values[x]
                    for x in range(N)), 'division-free even normal form')
        kind = 'even_normal_form'; exact = Q(3, 4); bound = Q(3, 4)
        representation = (beta, d, u)
        require(4 * energy == 3 * N ** 3, 'arbitrary-target parity endpoint')
    else:
        kind = 'upper_bound'; exact = None
        if N == 3:
            numerator_bound = 19
            require(Qh[1] <= 5, 'N=3 arbitrary-target histogram bound')
        elif N == 4:
            numerator_bound = 44
            require(Qh[1] <= 10 and Qh[2] <= 8, 'N=4 involution histogram bound')
        elif N == 5:
            numerator_bound = 93
            require(all(Qh[h] <= 17 for h in range(1, 5)), 'N=5 arbitrary-target bound')
        elif N == 6:
            require(Qh[2] <= 20, 'N=6 two three-cycles exclude five plus one')
            if len(histograms[3]) == 1:
                numerator_bound = 152
                require(Qh[1] <= 20 and all(v % 2 == 0 for v in histograms[1].values()),
                        'N=6 constant shift-three yields even multiplicities')
            else:
                numerator_bound = 148
                require(Qh[1] <= 26 and Qh[3] <= 20, 'N=6 nonconstant involution case')
        else:
            raise RuntimeError('N=1,2 must have an affine or even normal form')
        require(energy <= numerator_bound, 'small arbitrary-target energy upper bound')
        require(4 * numerator_bound < 3 * N ** 3, 'strict arbitrary-target 3/4 comparison')
        bound = Q(numerator_bound, N ** 3)
    return {'N': N, 'target_modulus': target_modulus, 'kind': kind, 'exact_r': exact,
            'uniform_energy': energy, 'ordinary_energy': N ** 3,
            'uniform_ratio': Q(energy, N ** 3), 'proved_upper_bound': bound,
            'representation': representation, 'Qh': Qh}


def abelian_parity_identity(N, weights, target_modulus=None):
    """The parity indicator in Z or Z/MZ with M>=3, including domain N=2."""
    modulus(N)
    if N % 2:
        raise ValueError('an even domain is required')
    if target_modulus is not None:
        integer(target_modulus, 'non-affine target modulus', 3, 32)
    weights = weight(N, weights)
    values = tuple(x % 2 for x in range(N))
    e = tuple(weights[x] if x % 2 == 0 else Q(0) for x in range(N))
    o = tuple(weights[x] if x % 2 else Q(0) for x in range(N))
    ee = _convolution(N, e, e); oo = _convolution(N, o, o)
    R = tuple(sum((e[x] * o[(x + h) % N] for x in range(N)), Q(0)) for h in range(N))
    squares = sum(((ee[x] - oo[x]) ** 2 for x in range(N)), Q(0)) / 4
    squares += sum(((R[h] - R[-h % N]) ** 2 for h in range(N)), Q(0)) / 2
    ordinary = additive_energy(N, weights)
    respected = target_respected_energy(N, values, weights, target_modulus)
    require(respected - Q(3, 4) * ordinary == squares, 'arbitrary-target exact parity SOS')
    require(squares >= 0, 'arbitrary-target parity lower bound')
    return {'ordinary': ordinary, 'respected': respected, 'gap': squares}


def check_abelian_targets():
    words = 0; n6_cases = set(); identities = 0
    for target in (None, 3, 4, 5, 7):
        for N in range(1, 7):
            for values in product(range(3), repeat=N):
                row = abelian_small_certificate(N, values, target); words += 1
                if N == 6 and row['kind'] == 'upper_bound':
                    n6_cases.add(row['proved_upper_bound'])
        for N in (2, 4, 6, 8):
            for weights in ((1,) * N, tuple(Q(x + 1, x + 2) for x in range(N))):
                row = abelian_parity_identity(N, weights, target); identities += 1
                if weights == (1,) * N:
                    require(row['gap'] == 0, 'arbitrary-target parity uniform equality')
    require(n6_cases == {Q(148, 216), Q(152, 216)}, 'both N=6 arbitrary-target histogram cases exercised')
    return {'small_words': words, 'targets': ('Z', 'Z/3Z', 'Z/4Z', 'Z/5Z', 'Z/7Z'),
            'parity_identities': identities, 'N6_bounds_exercised': tuple(sorted(n6_cases)),
            'N5_bound': Q(93, 125), 'N2_integer_parity_ratio': Q(3, 4),
            'arbitrary_target_8_over_11_classification_claimed': False}



def check_partial_domain_caveat():
    """A Sidon partial map need not have any affine ambient extension."""
    N = 7; support = (0, 1, 3); values = (0, 0, 0, 1, 0, 0, 0)
    quadruples = 0
    for x, y, z, t in product(support, repeat=4):
        if (x + y - z - t) % N == 0:
            quadruples += 1
            require(sorted((x, y)) == sorted((z, t)), 'all supported Sidon quadruples are trivial')
    extensions = sum(all(values[x] == (alpha * x + beta) % N for x in support)
                     for alpha in range(N) for beta in range(N))
    require(extensions == 0, 'partial Sidon map has no ambient affine extension')
    for supported_weights in ((1, 1, 1), (Q(1, 2), Q(2, 3), Q(3, 4))):
        weights = [Q(0)] * N
        for x, w in zip(support, supported_weights): weights[x] = w
        require(energy_ratio(N, values, weights) == 1, 'partial-domain relative equality')
    require(quadruples == 15, 'Sidon ordered quadruple count')
    return {'N': N, 'support': support, 'partial_values': (0, 0, 1),
            'ordered_additive_quadruples': quadruples, 'all_supported_quadruples_trivial': True,
            'ambient_affine_extensions': extensions, 'indicator_ratio': Q(1)}


def run_all():
    return {'status': 'passed', 'scope': 'Bounded exact regressions; arbitrary-parameter claims use the written proofs',
            'four_windows': check_four_windows(),
            'small_moduli': [classify_small_words(N) for N in range(1, 6)] + [classify_small_words(6, True)],
            'parity': check_parity(), 'sparse_witness': check_sparse_witness(),
            'graph_convolution': check_graph_convolution(), 'deletion_model': check_deletion_model(),
            'certificate_examples': [relative_energy_certificate(8, (0, 0, 0, 1, 0, 0, 0, 0)),
                                     relative_energy_certificate(8, tuple(x % 2 for x in range(8))),
                                     relative_energy_certificate(7, tuple((2 * x + 1) % 7 for x in range(7)))],
            'finite_surrogates': [finite_surrogate(E, Q(2, 3)) for E in FINITE_EXPONENTS],
            'abelian_targets': check_abelian_targets(),
            'partial_domain_caveat': check_partial_domain_caveat(),
            'actual_theorem_exponent_constructed': False}


def _jsonable(value):
    if type(value) is Q:
        return str(value.numerator) + '/' + str(value.denominator)
    if type(value) is dict:
        return {k: _jsonable(v) for k, v in value.items()}
    if type(value) in (list, tuple):
        return [_jsonable(v) for v in value]
    return value


def main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    if type(argv) is not list or argv:
        raise SystemExit('This bounded diagnostic CLI takes no arguments')
    print(json.dumps(_jsonable(run_all()), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
