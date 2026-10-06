#!/usr/bin/env python3
"""Exact, offline, standard-library verifier for Report175 (Python >= 3.10).

New implementation prepared for this report, 2026-10-03. No third-party source
code is incorporated. Polynomial coefficients are always in ascending order.
Every check uses an explicit exception and therefore remains active under -O.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path
import sys


class VerificationError(Exception):
    """A certificate, invariant, or input check failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def trim(a):
    a = list(a)
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a or [0]


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        c[i] += v
    for i, v in enumerate(b):
        c[i] += v
    return trim(c)


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)


def power(a, n):
    c = [1]
    for _ in range(n):
        c = mul(c, a)
    return c


def divmod_q(a, b):
    a, b = list(map(Fraction, trim(a))), list(map(Fraction, trim(b)))
    require(b != [0], 'polynomial division by zero')
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while a != [0] and len(a) >= len(b):
        k = len(a) - len(b)
        t = a[-1] / b[-1]
        q[k] += t
        for j, v in enumerate(b):
            a[k + j] -= t * v
        a = trim(a)
    return trim(q), a


def primitive(a):
    a = trim(a)
    require(all(type(x) is int for x in a), 'noninteger PRS input')
    content = 0
    for v in a:
        content = gcd(content, abs(v))
    if not content:
        return [0]
    if a[-1] < 0:
        content = -content
    return [v // content for v in a]


def gcd_q(a, b):
    """Primitive pseudo-remainder sequence: exact gcd in Q[z], no floats."""
    a, b = primitive(a), primitive(b)
    while b != [0]:
        r = a[:]
        while r != [0] and len(r) >= len(b):
            shift, lead = len(r) - len(b), r[-1]
            r = [v * b[-1] for v in r]
            for j, v in enumerate(b):
                r[shift + j] -= lead * v
            r = primitive(r)  # Nonzero rational scaling preserves Q-remainders.
        a, b = b, r
    return a


def evaluate(a, x):
    v = 0
    for c in reversed(a):
        v = v * x + c
    return v


def derivative(a):
    return trim([i * a[i] for i in range(1, len(a))])


def divisors(n):
    require(type(n) is int and n != 0, 'divisors require a nonzero integer')
    n = abs(n)
    positive = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            positive.append(d)
            if d * d != n:
                positive.append(n // d)
    return sorted(positive + [-d for d in positive])


def irreducible_small(a):
    """Complete Q-irreducibility decision for our constant-one, degree<=4 data.

    Gauss's lemma and the rational-root theorem settle degrees 2 and 3. A
    reducible root-free quartic must have an integer quadratic factor g.
    Then g(0),g(1),g(-1) divide f(0),f(1),f(-1); interpolation enumerates
    every candidate. This is a finite exact test, not a probabilistic test.
    """
    require(a == trim(a) and a[0] == 1, 'factor must have constant term one')
    degree = len(a) - 1
    require(1 <= degree <= 4, 'factor degree outside bounded verifier scope')
    if degree == 1:
        return True
    for numerator in (-1, 1):
        for denominator in divisors(a[-1]):
            if evaluate(a, Fraction(numerator, denominator)) == 0:
                return False
    if degree <= 3:
        return True
    # No rational roots: the three values below are all nonzero.
    for c, plus, minus in product(divisors(a[0]), divisors(evaluate(a, 1)),
                                  divisors(evaluate(a, -1))):
        if (plus + minus - 2*c) % 2 or (plus - minus) % 2:
            continue
        b = (plus - minus) // 2
        leading = (plus + minus - 2*c) // 2
        if leading and divmod_q(a, [c, b, leading])[1] == [0]:
            return False
    return True


def transpose(a):
    return [list(col) for col in zip(*a)]


def mm(a, b):
    require(bool(a) and bool(b) and len(a[0]) == len(b), 'matrix shape mismatch')
    bt = transpose(b)
    return [[sum(x*y for x, y in zip(row, col)) for col in bt] for row in a]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matrix_add(a, b):
    return [[x+y for x, y in zip(row, other)] for row, other in zip(a, b)]


def scaled(a, c):
    return [[c*x for x in row] for row in a]


def determinant_polynomial(a):
    """det(I-z A), exact Faddeev-LeVerrier, including all n+1 coefficient slots."""
    n = len(a)
    require(all(len(row) == n for row in a), 'nonsquare determinant input')
    b, coefficients = identity(n), [1]
    for k in range(1, n + 1):
        ab = mm(a, b)
        trace = sum(ab[i][i] for i in range(n))
        require(trace % k == 0, 'nonintegral characteristic coefficient')
        coefficient = -trace // k
        coefficients.append(coefficient)
        b = matrix_add(ab, scaled(identity(n), coefficient))
    require(all(x == 0 for row in b for x in row), 'matrix CH identity failed')
    return coefficients


def attack(p, q):
    return abs(p[0] - q[0]) <= 1 and abs(p[1] - q[1]) <= 1


def physical_states(h):
    """Enumerate four physical square choices per block; derive labels afterward."""
    found = {}
    choices = tuple(product(range(2), repeat=2))
    for offsets in product(choices, repeat=h):
        points = tuple((2*i+a, b) for i, (a, b) in enumerate(offsets))
        if any(attack(p, q) for p, q in combinations(points, 2)):
            continue
        vertical = tuple(a for a, _ in offsets)
        u = vertical.count(0)
        require(vertical == (0,)*u + (1,)*(h-u), 'physical threshold bijection')
        key = (tuple(b for _, b in offsets), u)
        require(key not in found, 'duplicate physical state')
        found[key] = points
    keys = sorted(found, key=lambda state: (sum(state[0]), state[0], state[1]))
    require(len(keys) == (h+1)*2**h, 'physical state count')
    return keys, [found[key] for key in keys]


def threshold_rule(left, right):
    b, u = left
    c, v = right
    if any(x > y for x, y in zip(b, c)):
        return False
    if u < v:
        return not any(b[i] == 1 and c[i+1] == 0 for i in range(u, v-1))
    return not any(b[i+1] == 1 and c[i] == 0 for i in range(v, u-1))


def build_transfer(h):
    keys, points = physical_states(h)
    shifted = [tuple((r, c+2) for r, c in right) for right in points]
    successors = []
    for i, left in enumerate(points):
        current = []
        for j, right in enumerate(shifted):
            geometric = not any(attack(p, q) for p in left for q in right)
            require(geometric == threshold_rule(keys[i], keys[j]),
                    f'h={h}: physical/threshold pair {i},{j}')
            if geometric:
                current.append(j)
        successors.append(current)
    return keys, successors


def sequence(successors, length):
    vector, result = [1]*len(successors), []
    for _ in range(length):
        result.append(sum(vector))
        new = [0]*len(vector)
        for value, destinations in zip(vector, successors):
            for j in destinations:
                new[j] += value
        vector = new
    return result


def component_incidence(word, color):
    """Independent union-find construction of monochromatic path components."""
    n, parent = len(word)+1, list(range(len(word)+1))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for i, edge_color in enumerate(word):
        if edge_color == color:
            parent[root(i+1)] = root(i)
    parts = sorted({root(i) for i in range(n)})
    return [[int(root(i) == p) for p in parts] for i in range(n)]


def gram_block(word, block):
    h, n = len(word), len(word)+1
    x0, x1 = component_incidence(word, 0), component_incidence(word, 1)
    c = mm(transpose(x0), x1)
    require((len(c), len(c[0])) == (sum(word)+1, h-sum(word)+1), 'component dimensions')
    require(all(v in (0, 1) for row in c for v in row), 'component intersections not 0/1')
    require(sum(map(sum, c)) == n, 'component incidence edge count')
    e0, e1 = mm(x0, transpose(x0)), mm(x1, transpose(x1))
    require(block == mm(e0, e1) == mm(mm(x0, c), transpose(x1)), 'Gram factorization')
    if len(c) <= len(c[0]):
        u, v, g = x0, mm(c, transpose(x1)), mm(c, transpose(c))
    else:
        u, v, g = mm(x0, c), transpose(x1), mm(transpose(c), c)
    require(mm(u, v) == block and mm(v, u) == g and g == transpose(g), 'UV/VU identities')
    full_d, d = determinant_polynomial(block), determinant_polynomial(g)
    require(trim(full_d) == trim(d), 'determinant identity')
    # Polynomial Woodbury identity: (I-zM)[dI+zU adj(I-zG)V]=dI.
    r, adj = len(g), [identity(len(g))]
    for k in range(1, r):
        adj.append(matrix_add(mm(g, adj[-1]), scaled(identity(r), d[k])))
    zero = scaled(identity(n), 0)
    numerator = [scaled(identity(n), coeff) for coeff in d]
    for k in range(r):
        numerator[k+1] = matrix_add(numerator[k+1], mm(mm(u, adj[k]), v))
    for k in range(len(numerator)+1):
        lhs = numerator[k] if k < len(numerator) else zero
        if k:
            lhs = matrix_add(lhs, scaled(mm(block, numerator[k-1]), -1))
        rhs = scaled(identity(n), d[k]) if k < len(d) else zero
        require(lhs == rhs, 'polynomial diagonal resolvent identity')
    return trim(d)


def row_counts(h, max_w):
    """Independent all-cardinality DP on physical rows of width 2h.

    Keeps every attainable number of kings; it does not assume maximum density,
    encode 2x2 blocks, or call the transfer/threshold implementation.
    """
    width = 2*h
    masks = [m for m in range(1 << width) if not (m & (m << 1))]
    sizes = [m.bit_count() for m in masks]
    predecessors = [[j for j, prev in enumerate(masks)
                     if not (prev & (cur | (cur << 1) | (cur >> 1)))]
                    for cur in masks]
    dp = [[0] for _ in masks]
    dp[masks.index(0)] = [1]
    result = []
    for rows in range(1, 2*max_w+1):
        nxt = []
        for weight, pred in zip(sizes, predecessors):
            total = [0] * (max(len(dp[j]) for j in pred) + weight)
            for j in pred:
                for k, ways in enumerate(dp[j]):
                    total[k+weight] += ways
            nxt.append(trim(total))
        dp = nxt
        if rows % 2 == 0:
            distribution = [0] * max(map(len, dp))
            for row in dp:
                for k, ways in enumerate(row):
                    distribution[k] += ways
            distribution = trim(distribution)
            require(len(distribution)-1 == h*rows//2, 'physical-row maximum cardinality')
            result.append(distribution[-1])
    return result


def validate_polynomial(a, description):
    require(isinstance(a, list) and bool(a), f'{description}: missing coefficient list')
    require(all(type(x) is int for x in a), f'{description}: coefficients must be integers')
    require(trim(a) == a, f'{description}: trailing zero')
    return a


def verify_factors(polynomial, factors, h, rank=None):
    require(isinstance(factors, list) and bool(factors), 'missing factor list')
    result, seen = [1], set()
    maxima = {}
    for entry in factors:
        f = validate_polynomial(entry['coefficients'], 'factor')
        exponent = entry['exponent']
        require(type(exponent) is int and exponent >= 1, 'invalid factor exponent')
        require(tuple(f) not in seen, 'duplicate factor entry')
        seen.add(tuple(f))
        degree = len(f)-1
        require(irreducible_small(f), 'claimed factor is reducible over Q')
        require(degree <= h//2+1, 'factor degree bound')
        if rank is None:
            require(exponent <= h-2*degree+3, 'factor multiplicity bound')
            maxima[str(degree)] = max(maxima.get(str(degree), 0), exponent)
        else:
            require(degree-1 <= rank <= h-degree+1, 'Gram rank/degree restriction')
        result = mul(result, power(f, exponent))
    require(result == polynomial, 'factor product differs from denominator/determinant')
    return maxima


def certify_gf(successors, numerator, denominator, onset):
    """Prove F=z sum(s_n z^n)=P/Q by N consecutive CH residuals.

    Onset L can exceed deg(Q). Keeping all L numerator slots accommodates zero
    eigenvalue transients. For j>=0 the residual is 1^T T^j V, where
    V=sum_i q_i T^(L-i)1 (or the transpose orientation used by sequence()).
    Cayley-Hamilton for the N-state T propagates its first N zeros forward.
    """
    require(numerator[0] == 0 and denominator[0] == 1, 'GF normalization')
    require(type(onset) is int and onset >= max(len(denominator)-1, len(numerator)-1),
            'recurrence onset omits denominator degree or numerator transient')
    require(onset <= len(successors), 'recurrence onset exceeds transfer-state bound')
    n = len(successors)
    seq = sequence(successors, max(onset+n, 6))
    convolution = [sum(denominator[i]*seq[k-i]
                      for i in range(min(k, len(denominator)-1)+1))
                   for k in range(onset+n)]
    expected = trim([0] + convolution[:onset])
    require(expected == numerator, 'GF numerator mismatch')
    require(all(x == 0 for x in convolution[onset:onset+n]), 'N-state CH residual certificate')
    require(gcd_q(numerator, denominator) == [1], 'GF numerator/denominator not coprime')
    return seq


def dominant_coefficients(h, numerator, denominator):
    n, pole = h+1, Fraction(1, h+1)
    reduced, remainder = divmod_q(denominator, [1, -2*n, n*n])
    require(remainder == [0] and evaluate(reduced, pole) != 0, 'dominant pole not exactly double')
    p, r = evaluate(numerator, pole), evaluate(reduced, pole)
    alpha = p/r
    slope = (evaluate(derivative(numerator), pole)*r - p*evaluate(derivative(reduced), pole))/(r*r)
    beta = alpha - slope/n
    require(alpha >= 1, 'dominant coefficient positivity/lower bound')
    return alpha, beta


def verify_height(entry):
    h = entry['h']
    require(type(h) is int and 1 <= h <= 6, 'unsupported height')
    keys, successors = build_transfer(h)
    n = len(keys)
    require(entry['states'] == n, 'recorded state count')
    edges = sum(map(len, successors))
    require(entry['allowed_pairs'] == edges, 'recorded transfer edge count')
    p = validate_polynomial(entry['numerator'], 'numerator')
    q = validate_polynomial(entry['denominator'], 'denominator')
    seq = certify_gf(successors, p, q, entry['recurrence_onset'])
    require(seq[:6] == entry['counts_w_1_to_6'], 'recorded initial counts')
    require(row_counts(h, 6) == seq[:6], 'independent all-cardinality physical-row counts')
    maxima = verify_factors(q, entry['factors'], h)
    require(maxima == entry['maximum_exponents_by_degree'], 'recorded exponent maxima')
    certificates = entry['gram_blocks']
    require(isinstance(certificates, list) and len(certificates) == 2**h, 'Gram certificate count')
    by_word = {item['word']: item for item in certificates}
    require(len(by_word) == len(certificates), 'duplicate Gram word')
    key_index = {key: i for i, key in enumerate(keys)}
    for word in product((0, 1), repeat=h):
        indices = [key_index[(word, u)] for u in range(h+1)]
        block = [[int(j in successors[i]) for j in indices] for i in indices]
        d = gram_block(word, block)
        cert = by_word[''.join(map(str, word))]
        require(validate_polynomial(cert['determinant'], 'Gram determinant') == d, 'Gram determinant data')
        verify_factors(d, cert['factors'], h, sum(word))
    alpha, beta = dominant_coefficients(h, p, q)
    require(str(alpha) == entry['alpha'] and str(beta) == entry['beta'], 'dominant coefficient data')
    return {'h': h, 'states': n, 'physical_pairs_checked': n*n,
            'allowed_pairs': edges, 'CH_residuals_checked': n,
            'recurrence_onset': entry['recurrence_onset'],
            'denominator_degree': len(q)-1, 'maximum_exponents_by_degree': maxima,
            'counts_w_1_to_6': seq[:6], 'alpha': str(alpha), 'beta': str(beta)}


def expect_failure(call, label):
    try:
        call()
    except VerificationError:
        return
    raise VerificationError(f'guard failed to reject {label}')


def self_tests():
    require(gcd_q([2, 3, 1], [1, 1]) == [1, 1], 'nontrivial polynomial gcd test')
    require(gcd_q([1, 0, 1], [1, 1]) == [1], 'coprime polynomial gcd test')
    require(not irreducible_small([1, 0, 2, 0, 1]), 'quartic quadratic split test')
    require(irreducible_small([1, -7, 13, -7, 1]), 'quartic irreducibility test')
    expect_failure(lambda: require(False, 'active under -O'), 'explicit invariant')
    # Nilpotent transfer: F(z)=2z+z^2, Q=1. It requires L=2, not deg(Q)=0.
    nilpotent = [[1], []]
    require(certify_gf(nilpotent, [0, 2, 1], [1], 2)[:4] == [2, 1, 0, 0], 'transient-safe certificate')
    expect_failure(lambda: certify_gf(nilpotent, [0, 2, 1], [1], 0), 'omitted zero-eigenvalue transient')
    expect_failure(lambda: certify_gf(nilpotent, [0, 2, 2], [1], 2), 'wrong numerator')
    expect_failure(lambda: certify_gf(nilpotent, [0, 2, 1], [1, -1], 2), 'wrong residual')
    expect_failure(lambda: validate_polynomial([True, 1], 'bad'), 'Boolean coefficient')
    expect_failure(lambda: verify_factors([1, 0, 2, 0, 1],
                   [{'coefficients': [1, 0, 2, 0, 1], 'exponent': 1}], 6), 'reducible claimed factor')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extended', action='store_true', help='explicitly permit heights 5 and 6; default max is 4')
    parser.add_argument('--max-h', type=int, choices=range(1, 7), help='upper height (default 4, or 6 with --extended)')
    parser.add_argument('--data', type=Path, default=Path(__file__).resolve().parent/'data'/'certificates.json')
    parser.add_argument('--json', action='store_true', default=True, help='emit deterministic machine-readable results (default)')
    parser.add_argument('--text', dest='json', action='store_false', help='emit compact human-readable progress instead of JSON')
    parser.add_argument('--self-test-only', '--self-test', action='store_true', help='run arithmetic and rejection guards only')
    args = parser.parse_args(argv)
    maximum = args.max_h if args.max_h is not None else (6 if args.extended else 4)
    if maximum > 4 and not args.extended:
        parser.error('heights 5 and 6 require explicit --extended')
    self_tests()
    if args.self_test_only:
        print('SELF TESTS PASSED (including rejection and nilpotent-transient guards)')
        return 0
    data = json.loads(args.data.read_text(encoding='utf-8'))
    require(data['schema_version'] == 1, 'unsupported certificate schema')
    entries = data['heights']
    require(isinstance(entries, list) and maximum <= len(entries) <= 6 and
            [e['h'] for e in entries] == list(range(1, len(entries)+1)),
            'data must contain contiguous heights from 1, including the requested maximum')
    results = []
    for entry in entries[:maximum]:
        result = verify_height(entry)
        results.append(result)
        if not args.json:
            print(f"h={result['h']}: PASS; N={result['states']}, pairs={result['physical_pairs_checked']}, "
                  f"CH residuals={result['CH_residuals_checked']}, deg Q={result['denominator_degree']}", flush=True)
    output = {'all_checks_passed': True, 'max_h': maximum,
              'arithmetic': 'exact integers and Fraction; Python standard library only', 'results': results}
    if args.json:
        print(json.dumps(output, indent=2, sort_keys=True))
    else:
        print(f'ALL CHECKS PASSED for 1 <= h <= {maximum}; all six widths checked at each height')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (VerificationError, ValueError, KeyError, TypeError, OSError) as exc:
        print(f'VERIFICATION FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
