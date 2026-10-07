#!/usr/bin/env python3
"""Exact arithmetic for commutative binary operations up to relabeling.

Python >=3.9; standard library only. Public functions validate their inputs.
Empty products and 0**0 are 1. The empty operation is counted by count(0)=1;
normalized sectors are defined only at positive n. No assertion statements
are used: all verification remains active under python -O.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from math import comb, factorial, gcd, isqrt, lcm

Q = Fraction


def integer(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f'{name} must be an integer >= {minimum}')
    return value


def cycle_type(cycles, minimum=1):
    if not isinstance(cycles, (list, tuple)):
        raise ValueError('cycle type must be a list or tuple of integers')
    if any(type(k) is not int or k < minimum for k in cycles):
        raise ValueError(f'cycle lengths must be integers >= {minimum}')
    return tuple(sorted(cycles))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def partitions(n, minimum=1):
    """Nondecreasing integer partitions, including the empty partition of 0."""
    integer(n, 'n')
    integer(minimum, 'minimum', 1)
    yield from _partitions(n, minimum)


def _partitions(n, minimum):
    if n == 0:
        yield ()
    for k in range(minimum, n + 1):
        for tail in _partitions(n - k, k):
            yield (k,) + tail


@lru_cache(None)
def divisors(n):
    integer(n, 'n', 1)
    return tuple(sorted({d for k in range(1, isqrt(n) + 1)
                         if n % k == 0 for d in (k, n // k)}))


@lru_cache(None)
def mobius(n):
    integer(n, 'n', 1)
    answer, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            answer = -answer
            if n % p == 0:
                return 0
        p += 1
    return -answer if n > 1 else answer


def z_type(cycles):
    cycles = cycle_type(cycles)
    answer = 1
    for k, multiplicity in Counter(cycles).items():
        answer *= k**multiplicity * factorial(multiplicity)
    return answer


def fixed_points(cycles, power):
    cycles = cycle_type(cycles)
    integer(power, 'power', 1)
    return sum(k for k in cycles if power % k == 0)


def permutation(cycles):
    """Construct one permutation of the prescribed cycle type."""
    cycles = cycle_type(cycles)
    result, start = [], 0
    for k in cycles:
        result.extend(range(start + 1, start + k))
        result.append(start)
        start += k
    return tuple(result)


def pair_orbits(cycles):
    """Enumerate actual orbits of unordered pairs, including diagonal pairs.

    This walks a concrete permutation, with no cycle-index or trace formula.
    """
    return dict(_pair_orbits(cycle_type(cycles)))


@lru_cache(None)
def _pair_orbits(cycles):
    p = permutation(cycles)
    n = len(p)
    unseen = {(i, j) for i in range(n) for j in range(i, n)}
    histogram = Counter()
    while unseen:
        start = min(unseen)
        pair, length = start, 0
        while pair in unseen:
            unseen.remove(pair)
            length += 1
            i, j = p[pair[0]], p[pair[1]]
            pair = (min(i, j), max(i, j))
        require(pair == start, 'Orbit walk did not return to its start')
        histogram[length] += 1
    require(sum(k * v for k, v in histogram.items()) == n * (n + 1) // 2,
            'Pair-orbit walk did not exhaust its input set')
    return tuple(sorted(histogram.items()))


def trace_orbits(cycles):
    """Recover orbit counts by fixed-point traces and Moebius inversion.

    Fix(Sym^2(sigma^r)) = (Fix(sigma^r)^2 + Fix(sigma^(2r)))/2.
    This code does not construct a permutation or enumerate its pair orbits.
    """
    return dict(_trace_orbits(cycle_type(cycles)))


@lru_cache(None)
def _trace_orbits(cycles):
    period = lcm(*cycles) if cycles else 1
    histogram = {}
    for length in divisors(period):
        numerator = 0
        for r in divisors(length):
            f1 = sum(k for k in cycles if r % k == 0)
            f2 = sum(k for k in cycles if 2 * r % k == 0)
            require((f1 * f1 + f2) % 2 == 0, 'Nonintegral pair trace')
            numerator += mobius(length // r) * ((f1 * f1 + f2) // 2)
        require(numerator >= 0 and numerator % length == 0,
                'Nonintegral or negative inverted orbit multiplicity')
        if numerator:
            histogram[length] = numerator // length
    n = sum(cycles)
    require(sum(k * v for k, v in histogram.items()) == n * (n + 1) // 2,
            'Trace orbit lengths did not exhaust the input set')
    return tuple(sorted(histogram.items()))


def fixed_count(cycles, method='walk'):
    """Number of tables fixed by one permutation with this full cycle type."""
    cycles = cycle_type(cycles)
    if method not in ('walk', 'trace', 'grouped'):
        raise ValueError('method must be walk, trace, or grouped')
    answer = 1
    if method in ('walk', 'trace'):
        orbits = pair_orbits(cycles) if method == 'walk' else trace_orbits(cycles)
        for length, multiplicity in orbits.items():
            answer *= fixed_points(cycles, length)**multiplicity
        return answer
    # A third route: group within-cycle and between-cycle input pairs.
    mult = Counter(cycles)
    for i, mi in mult.items():
        exponent = (i * mi * mi + mi) // 2 if i % 2 else i * mi * mi // 2
        answer *= fixed_points(cycles, i)**exponent
        if i % 2 == 0:
            answer *= fixed_points(cycles, i // 2)**mi
        for j, mj in mult.items():
            if j < i:
                answer *= fixed_points(cycles, lcm(i, j))**(gcd(i, j) * mi * mj)
    return answer


def sector_fixed_count(n, mu):
    """Support-factorized fixed count, valid also when n=sum(mu)."""
    integer(n, 'n')
    mu = cycle_type(mu, 2)
    s = sum(mu)
    if n < s:
        raise ValueError('n must be at least the moved support')
    m = n - s
    answer = m**(m * (m + 1) // 2)
    for k, mk in Counter(mu).items():
        answer *= (m + fixed_points(mu, k))**(m * mk)
    for length, h in pair_orbits(mu).items():
        answer *= (m + fixed_points(mu, length))**h
    return answer


def sector(n, mu):
    """Exact normalized contribution T_mu(n); the empty sector equals one."""
    integer(n, 'n', 1)
    mu = cycle_type(mu, 2)
    if sum(mu) > n:
        raise ValueError('n must be at least the moved support')
    return Q(factorial(n) * sector_fixed_count(n, mu),
             factorial(n - sum(mu)) * z_type(mu) * n**(n * (n + 1) // 2))


def count(n, method='walk'):
    """Burnside count, independently computable using either exact route."""
    integer(n, 'n')
    if method not in ('walk', 'trace', 'grouped'):
        raise ValueError('method must be walk, trace, or grouped')
    total = sum((Q(fixed_count(p, method), z_type(p)) for p in partitions(n)), Q(0))
    require(total.denominator == 1, 'Burnside sum is not integral')
    return total.numerator


def sectors_through_defect(defect):
    integer(defect, 'defect')
    sectors = [mu for s in range(2, 2 * defect + 1) for mu in partitions(s, 2)
               if 1 <= s - len(mu) <= defect]
    return sorted(sectors, key=lambda mu: (sum(mu) - len(mu), sum(mu), mu))


def amplitude(mu, order=5):
    """Exact rational logarithmic and relative amplitude coefficients.

    Uses the displayed closed formula for L_r and the exponential derivative
    recurrence. The checker independently expands the original log factors.
    """
    mu = cycle_type(mu, 2)
    if not mu:
        raise ValueError('amplitude requires a nonempty moved cycle type')
    integer(order, 'order')
    s, c = sum(mu), len(mu)
    mult, h = Counter(mu), pair_orbits(mu)
    beta = s - c * s + sum(h.values()) + s * (s - 1) // 2
    constant = Q(3 * s * s, 4) - Q(s, 2) - c * s + sum(fixed_points(mu, k) for k in mu)
    logs = []
    for r in range(1, order + 1):
        value = -sum((Q(j**r, r) for j in range(s)), Q(0))
        value -= Q(s**(r + 2), 2 * (r + 2))
        value -= Q((1 - 2 * s) * s**(r + 1), 2 * (r + 1))
        value -= Q((s * s - s) * s**r, 2 * r)
        for k, mk in mult.items():
            a = s - fixed_points(mu, k)
            value += mk * (-Q(a**(r + 1), r + 1) + Q(s * a**r, r))
        for length, multiplicity in h.items():
            value -= Q(multiplicity * (s - fixed_points(mu, length))**r, r)
        logs.append(value)
    coefficients = [Q(1)]
    for j in range(1, order + 1):
        coefficients.append(sum((r * logs[r - 1] * coefficients[j - r]
                                 for r in range(1, j + 1)), Q(0)) / j)
    return {'mu': list(mu), 'defect': s - c, 'support': s,
            'moved_orbits': {str(k): v for k, v in h.items()},
            'beta': beta, 'C': str(constant), 'z': z_type(mu),
            'log_coeff': [str(v) for v in logs],
            'relative_coeff': [str(v) for v in coefficients]}


def direct_log_series(mu, order=5):
    """Formal Laurent expansion of exact factors, independent of L_r formula.

    Each log(1-a*t) is expanded rationally. Its coefficients are multiplied
    by the Laurent polynomial representing that factor's exponent.
    """
    mu = cycle_type(mu, 2)
    if not mu:
        raise ValueError('series requires a nonempty moved cycle type')
    integer(order, 'order')
    s, c = sum(mu), len(mu)
    raw = Counter()

    def add_log(base, exponent):
        for power in range(1, order + 3):
            coefficient = -Q(base**power, power)
            for shift, weight in exponent.items():
                if -1 <= power + shift <= order:
                    raw[power + shift] += coefficient * weight

    for j in range(s):
        add_log(j, {0: Q(1)})
    add_log(s, {-2: Q(1, 2), -1: Q(1 - 2 * s, 2), 0: Q(s * (s - 1), 2)})
    for k in mu:
        add_log(s - fixed_points(mu, k), {-1: Q(1), 0: Q(-s)})
    for length, multiplicity in trace_orbits(mu).items():
        add_log(s - fixed_points(mu, length), {0: Q(multiplicity)})
    return {k: raw[k] for k in range(-1, order + 1)}


def exponential_by_partitions(log_coefficients):
    """exp(sum L_r*t^r), using integer partitions rather than recurrence."""
    logs = tuple(Q(v) for v in log_coefficients)
    result = [Q(1)]
    for j in range(1, len(logs) + 1):
        value = Q(0)
        for p in partitions(j):
            term = Q(1)
            for k, mk in Counter(p).items():
                term *= logs[k - 1]**mk / factorial(mk)
            value += term
        result.append(value)
    return result


def rational_tail_lower(n, defect):
    """Rational L <= B_D(n), including odd n; exact comparisons R<=L are safe.

    Flooring each nonintegral exponent lowers the relevant positive term:
    n^floor(3-n/2) <= n^(3-n/2), and hence 1/(1-r_floor) <= 1/(1-r).
    This is a *lower* bound on the stated analytic bound, not a universal
    substitute for it. It is used only for the listed finite checks.
    """
    integer(n, 'n', 1)
    integer(defect, 'defect')
    a = defect + 1
    if n < max(8, 4 * a):
        raise ValueError('tail bound requires n >= max(8, 4*(D+1))')
    first = -a * n + a * (a + 2)
    ratio_floor = (6 - n) // 2
    second_floor = (16 * n - 3 * n * n) // 16
    return Q(n)**first / (1 - Q(n)**ratio_floor) + Q(n)**second_floor


def exhaustive_tables(n):
    """Enumerate every labeled table and its entire relabeling orbit, n<=3."""
    integer(n, 'n')
    if n > 3:
        raise ValueError('exhaustive enumeration is restricted to n <= 3')
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    lookup = {pair: i for i, pair in enumerate(pairs)}
    perms = list(permutations(range(n)))
    induced = [[lookup[tuple(sorted((p[i], p[j])))] for i, j in pairs] for p in perms]
    aut_distribution, classes = Counter(), {}
    nonrigid = good = exceptional = trans_sum = other_sum = 0
    weighted_nonrigid = weighted_exceptional = 0
    for law in product(range(n), repeat=len(pairs)):
        autos, transforms = [], []
        for p, pairmap in zip(perms, induced):
            transformed = [0] * len(pairs)
            for i, j in enumerate(pairmap):
                transformed[j] = p[law[i]]
            transformed = tuple(transformed)
            transforms.append(transformed)
            if transformed == law:
                autos.append(p)
        order = len(autos)
        require(order > 0 and factorial(n) % order == 0, 'Invalid automorphism order')
        aut_distribution[order] += 1
        canonical = min(transforms)
        if canonical in classes:
            require(classes[canonical] == order, 'Automorphism order changed under relabeling')
        classes[canonical] = order
        transpositions = sum(sum(p[i] != i for i in range(n)) == 2 for p in autos)
        others = order - 1 - transpositions
        trans_sum += transpositions
        other_sum += others
        if order > 1:
            nonrigid += 1
            weighted_nonrigid += order
        if order == 2 and transpositions == 1:
            good += 1
        if others > 0:
            exceptional += 1
            weighted_exceptional += order
    total = n**len(pairs)
    require(sum(aut_distribution.values()) == total, 'Exhaustive labeled total mismatch')
    require(len(classes) == count(n, 'trace'), 'Exhaustive isomorphism count mismatch')
    class_distribution = Counter(classes.values())
    for order, labeled in aut_distribution.items():
        require(class_distribution[order] * factorial(n) == labeled * order,
                'Exhaustive orbit-stabilizer count mismatch')
    mean = Q(sum(k * v for k, v in aut_distribution.items()), total)
    p_nonrigid = Q(nonrigid, total)
    q_nonrigid = Q(sum(v for k, v in class_distribution.items() if k > 1), len(classes))
    require(q_nonrigid == (p_nonrigid + mean - 1) / mean, 'Unlabeled change of measure failed')
    require(q_nonrigid == Q(weighted_nonrigid, total) / mean, 'Class weighted probability mismatch')
    if n >= 2:
        t2 = sector(n, (2,))
        tail = mean - 1 - t2
        require(Q(trans_sum, total) == t2, 'Transposition expectation mismatch')
        require(Q(other_sum, total) == tail, 'Other-symmetry expectation mismatch')
        require(0 <= t2 - Q(good, total) <= comb(n, 2) * tail, 'Good-event inequality failed')
        require(abs(p_nonrigid - t2) <= (comb(n, 2) + 1) * tail, 'Nonrigidity inequality failed')
        require(Q(weighted_exceptional, total) <= (comb(n, 2) + 2) * tail,
                'Exceptional class-weight inequality failed')
    return {'n': n, 'labeled_total': total, 'unlabeled_total': len(classes),
            'labeled_automorphism_order_counts': dict(sorted(aut_distribution.items())),
            'unlabeled_automorphism_order_counts': dict(sorted(class_distribution.items())),
            'sum_transposition_automorphisms': trans_sum,
            'sum_other_nonidentity_automorphisms': other_sum,
            'nonrigid_labeled': nonrigid, 'transposition_generated_order_two_labeled': good,
            'exceptional_labeled': exceptional, 'exceptional_automorphism_weight': weighted_exceptional,
            'P_labeled_nonrigid': str(p_nonrigid), 'Q_unlabeled_nonrigid': str(q_nonrigid),
            'p_good': str(Q(good, total)), 'Pr_Z': str(Q(exceptional, total)),
            'mean_automorphism_order': str(mean) if n > 0 else None}
