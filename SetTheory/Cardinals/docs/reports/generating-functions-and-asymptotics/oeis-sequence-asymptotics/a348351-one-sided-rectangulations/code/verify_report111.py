#!/usr/bin/env python3
"""Finite exact certificates for report111. Python standard library only.

This is a mathematical regression checker, not a proof assistant. Analytic limit
arguments, cone estimates, and G-function regularity are outside its scope.
Every guard is an explicit exception and remains active under python -O.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys


class CheckFailure(Exception):
    pass


COUNTS = defaultdict(int)


def need(condition, code, detail=''):
    COUNTS[code.split('.')[0]] += 1
    if not condition:
        raise CheckFailure(code + (': ' + detail if detail else ''))


class Q:
    """Exact ordered field Q(sqrt(17)); no floating-point approximation."""
    __slots__ = ('a', 'b')

    def __init__(self, a=0, b=0):
        if isinstance(a, Q):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = Fraction(a), Fraction(b)

    def __add__(self, other):
        other = Q(other)
        return Q(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-Q(other))

    def __rsub__(self, other):
        return Q(other) - self

    def __mul__(self, other):
        other = Q(other)
        return Q(self.a * other.a + 17 * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Q(other)
        denominator = other.a * other.a - 17 * other.b * other.b
        if denominator == 0:
            raise CheckFailure('arithmetic.zero-denominator')
        return self * Q(other.a / denominator, -other.b / denominator)

    def __rtruediv__(self, other):
        return Q(other) / self

    def __pow__(self, n):
        if type(n) is not int or n < 0:
            raise CheckFailure('arithmetic.invalid-power')
        result, base = Q(1), self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    def __eq__(self, other):
        other = Q(other)
        return self.a == other.a and self.b == other.b

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        # Opposite signs: compare squares of positive magnitudes exactly.
        difference = a * a - 17 * b * b
        return ((difference > 0) - (difference < 0)) * (1 if a > 0 else -1)

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __le__(self, other):
        return (self - other).sign() <= 0

    def __gt__(self, other):
        return (self - other).sign() > 0

    def __ge__(self, other):
        return (self - other).sign() >= 0

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def triple(self):
        d = math.lcm(self.a.denominator, self.b.denominator)
        return [int(self.a * d), int(self.b * d), d]

    def __repr__(self):
        return str(self.triple())


def keys(value, expected, label):
    need(type(value) is dict and set(value) == set(expected),
         'schema.inventory', label)


def integer(value, label):
    need(type(value) is int, 'schema.integer', label)


def sequence(value, size, label):
    need(type(value) is list and len(value) == size, 'schema.size', label)


def field(value, label):
    sequence(value, 3, label)
    for x in value:
        integer(x, label)
    a, b, d = value
    need(d > 0 and math.gcd(math.gcd(abs(a), abs(b)), d) == 1,
         'schema.field-canonical', label)
    return Q(Fraction(a, d), Fraction(b, d))


def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'schema.duplicate-key', key)
        result[key] = value
    return result


def load_fixture(path):
    try:
        data = json.loads(path.read_text(encoding='utf-8'),
                          object_pairs_hook=reject_duplicates,
                          parse_constant=lambda x: (_ for _ in ()).throw(
                              CheckFailure('schema.nonfinite-number: ' + x)))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise CheckFailure('schema.json: ' + str(exc)) from exc
    keys(data, ['schema_version', 'colors', 'edges', 'matrix', 'gamma', 'right',
                'stationary', 'conditional_drift', 'corrector', 'covariance',
                'rho', 'two_cos', 'two_cos_polynomial', 'conventions', 'oeis',
                'cycles', 'duality', 'connector', 'schedule', 'annulus'], 'top level')
    integer(data['schema_version'], 'schema_version')
    need(data['schema_version'] == 1, 'schema.version')
    sequence(data['colors'], 4, 'colors')
    need(data['colors'] == list('BRGW'), 'source.state-order')
    sequence(data['edges'], 24, 'edges')
    seen = set()
    for e in data['edges']:
        keys(e, ['from', 'to', 'delta'], 'edge')
        need(type(e['from']) is str and e['from'] in 'BRGW' and len(e['from']) == 1
             and type(e['to']) is str and e['to'] in 'BRGW' and len(e['to']) == 1,
             'schema.color')
        sequence(e['delta'], 2, 'delta')
        for v in e['delta']:
            integer(v, 'delta')
        edge = (e['from'], e['to'], *e['delta'])
        need(edge not in seen, 'schema.duplicate-edge')
        seen.add(edge)
    for label, rows, columns, algebraic in [
            ('matrix', 4, 4, False), ('conditional_drift', 4, 2, True),
            ('corrector', 4, 2, True), ('covariance', 2, 2, True)]:
        sequence(data[label], rows, label)
        for row in data[label]:
            sequence(row, columns, label)
            for v in row:
                (field if algebraic else integer)(v, label)
    for label in ['right', 'stationary']:
        sequence(data[label], 4, label)
        for value in data[label]:
            field(value, label)
    for label in ['gamma', 'rho', 'two_cos']:
        field(data[label], label)
    sequence(data['two_cos_polynomial'], 3, 'two_cos_polynomial')
    for v in data['two_cos_polynomial']:
        integer(v, 'two_cos_polynomial')
    keys(data['conventions'], ['offset', 'empty_term', 'length_shift',
         'initial_colors', 'terminal_color', 'endpoint', 'quadrant'], 'conventions')
    for k in ['offset', 'empty_term', 'length_shift']:
        integer(data['conventions'][k], k)
    sequence(data['conventions']['initial_colors'], 4, 'initial_colors')
    for color in data['conventions']['initial_colors']:
        need(type(color) is str and len(color) == 1 and color in 'BRGW', 'schema.color')
    sequence(data['conventions']['endpoint'], 2, 'endpoint')
    for v in data['conventions']['endpoint']:
        integer(v, 'endpoint')
    need(type(data['conventions']['terminal_color']) is str and
         type(data['conventions']['quadrant']) is str, 'schema.conventions')
    sequence(data['oeis'], 17, 'oeis')
    for v in data['oeis']:
        integer(v, 'oeis')
        need(v >= 0, 'schema.count-nonnegative')
    keys(data['cycles'], ['0', '+E', '-E', '+N', '-N'], 'cycles')
    for name, cycle in data['cycles'].items():
        sequence(cycle, 3, name)
        for e in cycle:
            sequence(e, 4, 'cycle edge')
            need(type(e[0]) is str and type(e[1]) is str and
                 e[0] in 'BRGW' and e[1] in 'BRGW' and
                 len(e[0]) == len(e[1]) == 1, 'schema.color')
            integer(e[2], 'cycle dx')
            integer(e[3], 'cycle dy')
    keys(data['duality'], ['reverse_displacement', 'numerator_state',
                          'denominator_state'], 'duality')
    integer(data['duality']['reverse_displacement'], 'reverse_displacement')
    need(data['duality']['numerator_state'] in ['from', 'to'] and
         data['duality']['denominator_state'] in ['from', 'to'], 'schema.duality')
    keys(data['connector'], ['terminal_extra', 'first_color', 'final_color'], 'connector')
    integer(data['connector']['terminal_extra'], 'terminal_extra')
    need(data['connector']['first_color'] in list('BRGW') and
         data['connector']['final_color'] in list('BRGW'), 'schema.connector')
    keys(data['schedule'], ['scale_ratio', 'stair_multiplicity'], 'schedule')
    for value in data['schedule'].values():
        integer(value, 'schedule')
    keys(data['annulus'], ['q', 'H', 'b', 'T', 'delta', 'geometric_denominator_power',
                           'middle_time_offset', 'first_hit_policy', 'north_step'], 'annulus')
    for key in ['q', 'H', 'b', 'T', 'geometric_denominator_power', 'middle_time_offset']:
        integer(data['annulus'][key], 'annulus.' + key)
    sequence(data['annulus']['north_step'], 2, 'annulus.north_step')
    for value in data['annulus']['north_step']:
        integer(value, 'annulus.north_step')
    field(data['annulus']['delta'], 'annulus.delta')
    need(data['annulus']['first_hit_policy'] in ['first', 'last'], 'schema.annulus-policy')
    return data


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def solve(A, b):
    n = len(b)
    rows = [[Q(x) for x in A[i]] + [Q(b[i])] for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j] != 0), None)
        need(pivot is not None, 'duality.poisson-invertibility')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        z = rows[j][j]
        rows[j] = [x / z for x in rows[j]]
        for i in range(n):
            if i != j:
                z = rows[i][j]
                rows[i] = [x - z * y for x, y in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


# Sparse Laurent polynomials in (x,y,t), with integer coefficients.
def add(A, B):
    out = dict(A)
    for monomial, value in B.items():
        out[monomial] = out.get(monomial, 0) + value
        if out[monomial] == 0:
            del out[monomial]
    return out


def mul(A, B):
    out = {}
    for a, av in A.items():
        for b, bv in B.items():
            monomial = tuple(x + y for x, y in zip(a, b))
            out[monomial] = out.get(monomial, 0) + av * bv
    return {k: v for k, v in out.items() if v}


def mon(x=0, y=0, t=0, c=1):
    return {(x, y, t): c} if c else {}


def determinant(A):
    out = {}
    for p in itertools.permutations(range(len(A))):
        inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
        term = mon(c=(-1)**inversions)
        for i, j in enumerate(p):
            term = mul(term, A[i][j])
        out = add(out, term)
    return out


def derivative_value(poly, orders, gamma):
    total = Q(0)
    for exponents, coefficient in poly.items():
        coefficient = Q(coefficient)
        new = list(exponents)
        for j, order in enumerate(orders):
            for _ in range(order):
                coefficient *= new[j]
                new[j] -= 1
        if coefficient != 0:
            need(new[2] >= 0, 'spectral.nonnegative-t-power')
            total += coefficient * gamma**new[2]
    return total


def source_model(data):
    # Independently reconstruct the intersection of the source's weak-leftmost
    # and weak-rightmost inequalities, NOT by copying the fixture table.
    C = list('BRGW')
    level = {'B': 1, 'R': 0, 'G': 0, 'W': -1}
    derived = set()
    for c in C:
        for d in C:
            xmin = 0 if c in 'BR' or d in 'BG' else -1
            ymin = 0 if c in 'BG' or d in 'BR' else -1
            for dx in range(xmin, level[c] - ymin + 1):
                derived.add((c, d, dx, level[c] - dx))
    supplied = {(e['from'], e['to'], *e['delta']) for e in data['edges']}
    need(derived == supplied, 'source.transitions', 'weak inequalities versus table')
    edges = sorted(derived)
    A = [[sum(e[0] == c and e[1] == d for e in edges) for d in C] for c in C]
    need(A == data['matrix'], 'source.matrix')
    need(all(x > 0 for row in mm(A, A) for x in row), 'source.primitivity')
    return C, edges, A


def algebra(data, C, edges, A):
    gamma = field(data['gamma'], 'gamma')
    r = [field(x, 'right') for x in data['right']]
    pi = [field(x, 'stationary') for x in data['stationary']]
    h = [[field(x, 'corrector') for x in row] for row in data['corrector']]
    Sigma = [[field(x, 'covariance') for x in row] for row in data['covariance']]
    need(gamma * gamma - 7 * gamma + 8 == 0 and gamma > Fraction(7, 2), 'pf.gamma')
    need(all(x > 0 for x in r) and r[3] == 1, 'pf.right-normalization')
    need(all(sum(A[i][j] * r[j] for j in range(4)) == gamma * r[i]
             for i in range(4)), 'pf.right-eigenvector')
    need(sum(r) == 3 + Q(0, 1), 'pf.sum-right')
    need(all(r[0] >= v for v in r), 'pf.black-maximum')
    weighted = [(C.index(c), C.index(d), dx, dy, r[C.index(d)] / (gamma * r[C.index(c)]))
                for c, d, dx, dy in edges]
    P = [[Q(0) for _ in C] for _ in C]
    for i, j, dx, dy, w in weighted:
        need(w > 0, 'pf.edge-positive')
        P[i][j] += w
    need(all(sum(row) == 1 for row in P), 'pf.edge-normalization')
    need(all(x > 0 for x in pi) and sum(pi) == 1, 'stationary.normalization')
    need(all(sum(pi[i] * P[i][j] for i in range(4)) == pi[j] for j in range(4)),
         'stationary.invariance')
    m = [[sum(w * (dx, dy)[v] for i, j, dx, dy, w in weighted if i == c)
          for v in range(2)] for c in range(4)]
    need(m == [[field(x, 'conditional_drift') for x in row] for row in data['conditional_drift']],
         'drift.conditional')
    need(all(sum(pi[c] * m[c][v] for c in range(4)) == 0 for v in range(2)),
         'drift.stationary-zero')
    need(all(h[i][v] - sum(P[i][j] * h[j][v] for j in range(4)) == m[i][v]
             for i in range(4) for v in range(2)), 'corrector.poisson')
    need(h[3] == [0, 0] and all(0 <= x < Fraction(3, 2) for row in h for x in row),
         'corrector.bound')
    calculated, conditional = covariance(weighted, pi, h, 'martingale')
    need(calculated == Sigma, 'covariance.effective')
    need(Sigma[0][1] == Sigma[1][0] and Sigma[0][0] > 0 and
         Sigma[0][0] * Sigma[1][1] - Sigma[0][1] * Sigma[1][0] > 0,
         'covariance.positive-definite')
    need(Sigma[0][0] == Sigma[1][1], 'covariance.exchange-symmetry')
    rho = field(data['rho'], 'rho')
    need(Sigma[0][1] / Sigma[0][0] == rho and 0 < rho < Fraction(1, 2),
         'covariance.correlation')
    need(any(conditional[i] != conditional[0] for i in range(1, 4)),
         'covariance.color-dependence')
    spectral = [[{} for _ in C] for _ in C]
    for i in range(4):
        spectral[i][i] = mon(t=1)
    for c, d, dx, dy in edges:
        i, j = C.index(c), C.index(d)
        spectral[i][j] = add(spectral[i][j], mon(dx, dy, c=-1))
    charpoly = determinant(spectral)
    AA = {(1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 0): 2, (-1, 0, 0): 1, (0, -1, 0): 1}
    BB = add(AA, {(1, -1, 0): 1, (-1, 1, 0): 1})
    cubic = add(add(mon(t=3), mul(mon(t=2, c=-1), AA)), add(mon(t=1), BB))
    need(charpoly == mul(mon(t=1), cubic), 'spectral.laurent-characteristic')
    at_one = defaultdict(int)
    for (x, y, t), value in charpoly.items():
        at_one[t] += value
    need({k: v for k, v in at_one.items() if v} == {4: 1, 3: -6, 2: 1, 1: 8},
         'spectral.characteristic-at-one')
    need(derivative_value(cubic, (0, 0, 0), gamma) == 0 and
         derivative_value(cubic, (1, 0, 0), gamma) == 0 and
         derivative_value(cubic, (0, 1, 0), gamma) == 0, 'spectral.centered-branch')
    ft = derivative_value(cubic, (0, 0, 1), gamma)
    need(ft != 0, 'spectral.simple-branch')
    hessian = [[-derivative_value(cubic, (int(i == 0) + int(j == 0),
                                               int(i == 1) + int(j == 1), 0), gamma)
                / (gamma * ft) for j in range(2)] for i in range(2)]
    need(hessian == Sigma, 'spectral.hessian-covariance')
    return gamma, r, pi, h, Sigma, weighted, P


def covariance(weighted, pi, h, group):
    V = [[[Q(0) for _ in range(2)] for _ in range(2)] for _ in range(4)]
    drift = [[Q(0), Q(0)] for _ in range(4)]
    for i, j, dx, dy, w in weighted:
        delta = [(dx, dy)[v] + h[j][v] - h[i][v] for v in range(2)]
        for v in range(2):
            if group == 'martingale':
                need(abs(delta[v]) < 3, 'martingale.increment-bound')
            drift[i][v] += w * delta[v]
            for u in range(2):
                V[i][v][u] += w * delta[v] * delta[u]
    need(all(x == 0 for row in drift for x in row), group + '.zero-drift')
    return [[sum(pi[i] * V[i][v][u] for i in range(4)) for u in range(2)] for v in range(2)], V


def walk_distribution(weighted, initial, steps, killed=True):
    distribution = {initial: Q(1)}
    by_color = defaultdict(list)
    for e in weighted:
        by_color[e[0]].append(e)
    for _ in range(steps):
        new = defaultdict(Q)
        for (x, y, c), w0 in distribution.items():
            for i, j, dx, dy, w in by_color[c]:
                if not killed or (x + dx >= 0 and y + dy >= 0):
                    new[x + dx, y + dy, j] += w0 * w
        distribution = new
    return distribution


def duality(data, weighted, pi, P, Sigma):
    config = data['duality']
    dual = []
    for i, j, dx, dy, w in weighted:
        numerator = pi[i if config['numerator_state'] == 'from' else j]
        denominator = pi[i if config['denominator_state'] == 'from' else j]
        dual.append((j, i, config['reverse_displacement'] * dx,
                     config['reverse_displacement'] * dy, numerator / denominator * w))
    for original, reversed_edge in zip(weighted, dual):
        i, j, dx, dy, w = original
        need(reversed_edge[:4] == (j, i, -dx, -dy), 'duality.reversed-edge')
        need(pi[i] * w == pi[j] * reversed_edge[4], 'duality.edge-balance')
    PD = [[sum(w for i, j, dx, dy, w in dual if i == c and j == d)
           for d in range(4)] for c in range(4)]
    need(all(sum(row) == 1 for row in PD), 'duality.normalization')
    need(all(sum(pi[i] * PD[i][j] for i in range(4)) == pi[j] for j in range(4)),
         'duality.stationary')
    md = [[sum(w * (dx, dy)[v] for i, j, dx, dy, w in dual if i == c)
           for v in range(2)] for c in range(4)]
    need(all(sum(pi[c] * md[c][v] for c in range(4)) == 0 for v in range(2)), 'duality.zero-mean')
    HD = [[Q(0), Q(0)] for _ in range(4)]
    matrix = [[int(i == j) - PD[i][j] for j in range(4)] for i in range(3)] + [[0, 0, 0, 1]]
    for v in range(2):
        solution = solve(matrix, [md[i][v] for i in range(3)] + [0])
        for i in range(4):
            HD[i][v] = solution[i]
    need(all(HD[i][v] - sum(PD[i][j] * HD[j][v] for j in range(4)) == md[i][v]
             for i in range(4) for v in range(2)), 'duality.poisson')
    need(all(abs(x) < 1 for row in HD for x in row), 'duality.corrector-bound')
    VD, _ = covariance(dual, pi, HD, 'duality')
    need(VD == Sigma, 'duality.covariance')
    # Entire killed kernels on this finite set, including zero-step identities.
    starts = [(x, y, c) for x, y in [(0, 0), (1, 0), (0, 1), (1, 1)] for c in range(4)]
    for length in range(4):
        forwards = {a: walk_distribution(weighted, a, length) for a in starts}
        backwards = {b: walk_distribution(dual, b, length) for b in starts}
        for a in starts:
            for b in starts:
                need(pi[a[2]] * forwards[a].get(b, Q(0)) == pi[b[2]] * backwards[b].get(a, Q(0)),
                     'duality.killed-kernel', 'length=' + str(length))
    return dual, HD


def counts(data, edges, gamma, r, weighted):
    convention = data['conventions']
    need(convention['offset'] == 0 and convention['empty_term'] == 1, 'count.offset')
    need(convention['length_shift'] == -1, 'count.indexing')
    need(convention['initial_colors'] == list('BRGW'), 'count.initial-states')
    need(convention['terminal_color'] == 'W', 'count.terminal-white')
    need(convention['endpoint'] == [0, 0] and convention['quadrant'] == 'closed', 'count.endpoint')
    distribution = {(0, 0, c): 1 for c in convention['initial_colors']}
    values = [1, distribution[0, 0, 'W']]
    for length in range(1, 16):
        new = defaultdict(int)
        for (x, y, c), value in distribution.items():
            for a, d, dx, dy in edges:
                if a == c and x + dx >= 0 and y + dy >= 0:
                    new[x + dx, y + dy, d] += value
        distribution = new
        values.append(distribution.get((0, 0, 'W'), 0))
    need(values == data['oeis'], 'count.oeis-prefix', str(values))
    forbidden = {(2, 4, 1, 3), (3, 1, 4, 2), (2, 1, 4, 3), (3, 4, 1, 2)}
    permutation_counts = []
    for n in range(8):
        count = 0
        for p in itertools.permutations(range(n)):
            bad = False
            for j in range(1, n - 2):
                for i in range(j):
                    for l in range(j + 2, n):
                        values4 = [p[i], p[j], p[j + 1], p[l]]
                        ranks = tuple(1 + sum(y < x for y in values4) for x in values4)
                        if ranks in forbidden:
                            bad = True
                            break
                    if bad:
                        break
                if bad:
                    break
            count += not bad
        permutation_counts.append(count)
        need(count == values[n], 'count.vincular-permutations', 'n=' + str(n))
    for length in range(6):
        mass = sum(r[c] * walk_distribution(weighted, (0, 0, c), length).get((0, 0, 3), Q(0))
                   for c in range(4))
        need(gamma**length * mass == values[length + 1], 'count.pf-transfer')
    need(all(('R', c, 0, 0) in edges for c in 'BRGW'), 'count.monotone-injection')
    return values, permutation_counts


def check_path(path, start, edges, code, quadrant=True):
    x, y, c = start
    for a, d, dx, dy in path:
        need(a == c and (a, d, dx, dy) in edges, code + '.edge')
        x, y, c = x + dx, y + dy, d
        need(not quadrant or (x >= 0 and y >= 0), code + '.quadrant')
    return x, y, c


def constructions(data, edges):
    need(('R', 'R', 0, 0) in edges, 'cycles.zero-loop')
    destinations = {'0': (0, 0), '+E': (1, 0), '-E': (-1, 0), '+N': (0, 1), '-N': (0, -1)}
    for name, cycle in data['cycles'].items():
        path = [tuple(e) for e in cycle]
        need(check_path(path, (0, 0, 'R'), edges, 'cycles', False) == (*destinations[name], 'R'),
             'cycles.displacement', name)
    cfg = data['connector']
    connector_cases = 0
    for H in range(1, 9):
        initial = [('B', 'B', 1, 0)] * H + [('B', 'B', 0, 1)] * H
        need(check_path(initial, (0, 0, 'B'), edges, 'connector.initial') == (H, H, 'B'),
             'connector.initial-endpoint')
        D = 4 * H + cfg['terminal_extra']
        for x in range(H, 2 * H + 1):
            for y in range(H, 2 * H + 1):
                for c in 'BRGW':
                    dx = {'B': 1, 'R': 0, 'G': 0, 'W': -1}[c]
                    padding = D - (2 + x + dx + y)
                    need(padding >= 0, 'connector.padding-size')
                    red, white = cfg['first_color'], cfg['final_color']
                    path = [(c, red, dx, 0)] + [(red, red, 0, 0)] * padding + [(red, white, 0, 0)]
                    path += [(white, white, -1, 0)] * (x + dx) + [(white, white, 0, -1)] * y
                    need(len(path) == D, 'connector.exact-length')
                    need(check_path(path, (x, y, c), edges, 'connector.terminal') == (0, 0, 'W'),
                         'connector.terminal-endpoint')
                    connector_cases += 1
    # Small exhaustive checks of the variable-padding injection, with complete
    # histories and recovery of the first black vertex and fixed middle length.
    injection_cases = 0
    for H in [1, 2]:
        raw = [([], (0, 0, 'B'))]
        for k in range(4):
            L = k + 6 * H + 2
            images = set()
            for middle, endpoint in raw:
                x, y, c = endpoint
                prefix = [('B', 'B', 1, 0)] * H + [('B', 'B', 0, 1)] * H
                endx, endy = x + H, y + H
                suffix = []
                if c == 'B':
                    suffix.append(('B', 'W', 1, 0))
                    endx += 1
                elif c in 'RG':
                    suffix.append((c, 'W', 0, 0))
                suffix += [('W', 'W', -1, 0)] * endx + [('W', 'W', 0, -1)] * endy
                slack = L - len(prefix) - len(middle) - len(suffix)
                need(slack >= 0, 'injection.padding-size')
                padding = [('R', 'R', 0, 0)] * (slack - 1) + [('R', 'B', 0, 0)] if slack else []
                path = padding + prefix + middle + suffix
                need(len(path) == L, 'injection.exact-length')
                start = (0, 0, 'R' if slack else 'B')
                need(check_path(path, start, edges, 'injection') == (0, 0, 'W'), 'injection.endpoint')
                vertices = [start[2]] + [e[1] for e in path]
                first_black = vertices.index('B')
                need(path[first_black + 2 * H:first_black + 2 * H + k] == middle, 'injection.recovery')
                key = (start, tuple(path))
                need(key not in images, 'injection.injectivity')
                images.add(key)
                injection_cases += 1
            nxt = []
            for path, (x, y, c) in raw:
                for edge in edges:
                    a, d, dx, dy = edge
                    if a == c and abs(x + dx) <= H and abs(y + dy) <= H:
                        nxt.append((path + [edge], (x + dx, y + dy, d)))
            raw = nxt
    return connector_cases, injection_cases


def ceil_sqrt(n):
    root = math.isqrt(n)
    return root + int(root * root != n)


def schedules(data):
    scale, multiplier = data['schedule']['scale_ratio'], data['schedule']['stair_multiplicity']
    need(scale == 2 and multiplier == 2, 'schedule.definition')
    cases = 0
    for H0 in range(1, 13):
        tests = set(range(H0 * H0, 4097))
        for j in range(1, 101):
            boundary = H0 * H0 * 4**j
            tests.update([boundary - 1, boundary, boundary + 1])
        tests.update([10**100, 10**300])
        for length in sorted(tests):
            H, J, stair_oneway = H0, 0, 0
            while scale * scale * H * H <= length:
                stair_oneway += H * H
                H *= scale
                J += 1
            stair = multiplier * stair_oneway
            T = length - stair
            need(H * H <= length < 4 * H * H, 'schedule.scale-selection')
            need(3 * stair == 2 * (H * H - H0 * H0), 'schedule.geometric-identity')
            need(H * H <= 3 * T and T <= 4 * H * H, 'schedule.central-bounds')
            D = 4 * H0 + 3
            L = length + 2 * H0 + D
            need(2 * H0 + stair_oneway + T + stair_oneway + D == L, 'schedule.original-time')
            cases += 1
    # Exact floor(L-72*sqrt(L)-20) and ceil(12*sqrt(k)+2).
    square_tests = list(range(6000, 10001))
    square_tests += [10**j + delta for j in range(4, 151, 7) for delta in [-1, 0, 1]]
    for n in square_tests:
        L = n - 1
        k = L - 20 - ceil_sqrt(5184 * L)
        need(k >= 1, 'schedule.elementary-positive-k')
        H = ceil_sqrt(144 * k) + 2
        need(k + 6 * H + 2 <= L, 'schedule.elementary-padding')
    # Exact splitting and concatenation at ALL tested integer endpoint times.
    bridge_cases = 0
    for n in range(4, 161):
        n1 = n // 3
        n2 = (n - n1) // 2
        n3 = n - n1 - n2
        need(n1 + n2 + n3 == n and min(n1, n2, n3) >= 1, 'schedule.three-parts')
        for t in range(n // 4 + 1):
            for u in range(n // 4 + 1):
                m = n - t - u
                need(2 * m >= n and m <= n and t + m + u == n, 'schedule.exact-bridge-time')
                bridge_cases += 1
    return cases, len(square_tests), bridge_cases


def annuli(data, edges, Sigma):
    # Illustrative finite schedules, NOT values of analytic FCLT/Brownian constants.
    cfg = data['annulus']
    q, H, b, T = (cfg[k] for k in ['q', 'H', 'b', 'T'])
    q, b, T = Fraction(q), Fraction(b), Fraction(T)
    need(q >= 2, 'annulus.q-at-least-two')
    need(type(H) is int and H >= 1 and b > 0 and T > 0,
         'annulus.positive-parameters')
    delta = field(cfg['delta'], 'annulus.delta')
    need(delta > 0, 'annulus.positive-delta')
    determinant = Sigma[0][0]*Sigma[1][1]-Sigma[0][1]*Sigma[1][0]
    need(determinant > 0, 'annulus.positive-metric')
    inverse = [[Sigma[1][1]/determinant, -Sigma[0][1]/determinant],
               [-Sigma[1][0]/determinant, Sigma[0][0]/determinant]]
    def norm2(x, y):
        return inverse[0][0]*x*x+(inverse[0][1]+inverse[1][0])*x*y+inverse[1][1]*y*y
    # Squared whitened radii keep all calculations in Q(sqrt(17)).
    need(all(norm2(dx, dy) <= b*b for _, _, dx, dy in edges), 'annulus.step-bound')
    r02 = norm2(H, H)
    need(b*b < (q-1)**2*r02, 'annulus.no-skip')
    denominator = 1-q**(-cfg['geometric_denominator_power'])
    need(denominator > 0, 'annulus.geometric-denominator')
    need(T*delta*delta/denominator <= Fraction(1, 8), 'annulus.time-reserve')
    for J in range(13):
        radii2 = [r02*q**(2*j) for j in range(J+1)]
        total = sum(radii2[1:], Q(0))
        need(total == (radii2[-1]-r02)/denominator, 'annulus.geometric-sum')
        need(total <= radii2[-1]/denominator, 'annulus.geometric-bound')
        for radius2 in radii2:
            need(b*b < (q-1)**2*radius2, 'annulus.every-scale-no-skip')
    schedule_cases = 0
    for n in [10**6, 10**6+1, 10**8, 10**12, 10**18, 10**100, 10**300]:
        radius2, J = r02, 0
        need(radius2 <= delta*delta*n, 'annulus.base-scale-fits')
        while q*q*radius2 <= delta*delta*n:
            radius2, J = q*q*radius2, J+1
        need(delta*delta*n/(q*q) < radius2 <= delta*delta*n,
             'annulus.final-scale-bracket')
        total = 2*H+T*sum((r02*q**(2*j) for j in range(1, J+1)), Q(0))
        need(total <= Fraction(n, 4), 'annulus.prefix-time-quarter')
        need(b*b <= delta*delta*n, 'annulus.scaled-overshoot')
        schedule_cases += 1
    edges = set(edges)
    dual_edges = {(dst, src, -dx, -dy) for src, dst, dx, dy in edges}
    def vertices(path, start, rules, label):
        x, y, color = start
        out = [(x, y, color)]
        for src, dst, dx, dy in path:
            need(src == color and (src, dst, dx, dy) in rules, label+'.edge')
            x, y, color = x+dx, y+dy, dst
            need(x >= 0 and y >= 0, label+'.quadrant')
            out.append((x, y, color))
        return out
    seed_cases = 0
    for height in range(1, 17):
        for color, rules in [('B', edges), ('W', dual_edges)]:
            path = [(color, color, 1, 0)]*height+[(color, color, *cfg['north_step'])]*height
            pos = vertices(path, (0, 0, color), rules, 'annulus.seed')
            need(len(path) == 2*height and pos[-1] == (height, height, color),
                 'annulus.seed-endpoint-time')
            need(all(norm2(x, y) <= norm2(height, height) for x, y, _ in pos),
                 'annulus.seed-radius')
            seed_cases += 1
        for x, y in [(0, 0), (height, 0), (0, height), (height, height)]:
            need(norm2(x, y) <= norm2(height, height), 'annulus.seed-square-corners')
    need(inverse[0][0] == inverse[1][1], 'annulus.bisector-symmetry')
    # Actual original/dual path histories, with varying prefix lengths. The
    # middle segment crosses the selected radius repeatedly, so the recovery
    # test distinguishes FIRST hits from a mistaken last-hit convention.
    threshold2 = norm2(1, 1)
    prefixes = [[('B', 'B', 1, 0), ('B', 'B', 0, 1)]]
    dual_prefixes = [[('W', 'W', 1, 0), ('W', 'W', 0, 1)]]
    for k in range(3):
        prefixes.append([('B', 'R', 1, 0)]+[('R', 'R', 0, 0)]*k
                        +[('R', 'B', 0, 0), ('B', 'B', 0, 1)])
        dual_prefixes.append([('W', 'W', 1, 0), ('W', 'R', -1, 1)]
                             +[('R', 'R', 0, 0)]*k+[('R', 'W', 1, 0)])
    def hit(pos):
        times = [i for i, (x, y, _) in enumerate(pos) if norm2(x, y) >= threshold2]
        need(bool(times), 'annulus.radius-reached')
        return times[0] if cfg['first_hit_policy'] == 'first' else times[-1]
    images = set()
    for prefix, dual_prefix in itertools.product(prefixes, dual_prefixes):
        t, u, n = len(prefix), len(dual_prefix), 24
        pp = vertices(prefix, (0, 0, 'B'), edges, 'annulus.prefix')
        dp = vertices(dual_prefix, (0, 0, 'W'), dual_edges, 'annulus.dual-prefix')
        need(hit(pp) == t and hit(dp) == u, 'annulus.prefix-first-hits')
        m = n-t-u+cfg['middle_time_offset']
        need(t+m+u == n and n <= 2*m and m <= n, 'annulus.exact-middle-time')
        middle = [('B', 'R', 1, 0)]+[('R', 'R', 0, 0)]*(m-3)
        middle += [('R', 'W', 0, 0), ('W', 'W', -1, 0)]
        suffix = [(dst, src, -dx, -dy) for src, dst, dx, dy in reversed(dual_prefix)]
        path = prefix+middle+suffix
        pos = vertices(path, (0, 0, 'B'), edges, 'annulus.full-path')
        need(len(path) == n and pos[-1] == (0, 0, 'W'), 'annulus.exact-endpoint')
        need(4*t <= n and 4*u <= n and t <= n-u, 'annulus.disjoint-quarter-times')
        need(hit(pos) == t and hit(list(reversed(pos))) == u, 'annulus.first-hit-recovery')
        need(path[:t] == prefix and path[n-u:] == suffix, 'annulus.prefix-suffix-recovery')
        need(tuple(path) not in images, 'annulus.no-overcount')
        images.add(tuple(path))
    return {'annulus_schedule_cases': schedule_cases, 'annulus_seed_cases': seed_cases,
            'annulus_first_hit_concatenations': len(images)}


def angle_certificate(data):
    x = field(data['two_cos'], 'two_cos')
    rho = field(data['rho'], 'rho')
    need(x == -2 * rho, 'angle.cosine-sign')
    polynomial = data['two_cos_polynomial']
    need(polynomial == [2, 29, 1], 'angle.minimal-polynomial')
    need(sum(Q(c) * x**j for j, c in enumerate(polynomial)) == 0, 'angle.polynomial-root')
    discriminant = polynomial[1]**2 - 4 * polynomial[0] * polynomial[2]
    need(discriminant == 49 * 17 and math.isqrt(discriminant)**2 != discriminant,
         'angle.irreducibility-discriminant')
    conjugate = Q(x.a, -x.b)
    need(-2 < x < 0 and conjugate < -2, 'angle.conjugate-obstruction')
    need(sum(Q(c) * conjugate**j for j, c in enumerate(polynomial)) == 0, 'angle.conjugate-root')
    # The root-of-unity conjugate theorem is an analytic/algebraic proof premise,
    # not an assertion that a numerical arccos test proves irrationality.
    return {'two_cos': x.triple(), 'polynomial_low_to_high': polynomial,
            'discriminant': discriminant, 'conjugate': conjugate.triple(),
            'exact_bounds': '-2 < 2cos(theta) < 0; its other conjugate is < -2'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(path):
    data = load_fixture(path)
    C, edges, A = source_model(data)
    gamma, r, pi, h, Sigma, weighted, P = algebra(data, C, edges, A)
    dual, hd = duality(data, weighted, pi, P, Sigma)
    values, permutation_counts = counts(data, edges, gamma, r, weighted)
    connectors, injections = constructions(data, edges)
    scale_cases, padding_cases, bridge_cases = schedules(data)
    annulus_result = annuli(data, edges, Sigma)
    angle = angle_certificate(data)
    return {'status': 'PASS', 'arithmetic': 'integers, Fraction, and exact Q(sqrt(17)); no floats',
            'guards_active_under_optimization': True, 'guard_counts': dict(sorted(COUNTS.items())),
            'guards_total': sum(COUNTS.values()), 'fixture_sha256': sha256(path),
            'checker_sha256': sha256(Path(__file__).resolve()), 'oeis_n0_to_n16': values,
            'direct_vincular_permutations_n0_to_n7': permutation_counts,
            'terminal_connector_cases': connectors, 'padding_injection_cases': injections,
            'multiscale_integer_cases': scale_cases, 'elementary_sqrt_padding_cases': padding_cases,
            'exact_bridge_integer_cases': bridge_cases,
            'dual_corrector_W_zero': [[x.triple() for x in row] for row in hd],
            'covariance': [[x.triple() for x in row] for row in Sigma], 'angle_certificate': angle,
            'annulus_certificates': annulus_result,
            'scope': 'Finite identities and finite constructions only; no test certifies the FCLT, LLT, Brownian/cone bounds, logarithmic asymptotic theorem, G-function regularity, or non-D-finiteness deduction.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path, default=Path(__file__).with_name('report111_fixture.json'))
    args = parser.parse_args()
    try:
        result = run(args.fixture)
    except CheckFailure as exc:
        print('CHECK_FAIL ' + str(exc), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
