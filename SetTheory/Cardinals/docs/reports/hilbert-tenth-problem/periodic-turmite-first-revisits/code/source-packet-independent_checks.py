"""Independent standard-library audit. All checks survive python -O.

This checker uses direct integer geometry and a separately written evolving-board
simulator. It does not use the release collision(), colour_at(), brute(), or
snapshot_head() routines as correctness oracles.
"""
import itertools
import random
import unittest
from math import lcm

import observations as ob
from one_visit import Lane


def direct_atom(n, spec):
    low, high, residue, modulus = spec
    return n >= max(0, low) and (high is None or n <= high) and (n-residue) % modulus == 0


def direct_relation(a, b, n, chronological):
    if n < 0 or (a.last is not None and n > a.last):
        return False
    p = (a.p[0]+n*a.d[0], a.p[1]+n*a.d[1])
    if b.d == (0, 0):
        k = 0
    else:
        coordinate = 0 if b.d[0] else 1
        numerator = p[coordinate]-b.p[coordinate]
        if numerator % b.d[coordinate]:
            return False
        k = numerator // b.d[coordinate]
    return (k >= 0 and (b.last is None or k <= b.last)
            and p == (b.p[0]+k*b.d[0], b.p[1]+k*b.d[1])
            and (not chronological or b.t+b.period*k < a.t+a.period*n))


def direct_clause(clause, p, heading, board, tile):
    if clause.headings is not None and heading not in clause.headings:
        return False
    if clause.sites is not None and p not in clause.sites:
        return False
    for x, y, residue, modulus in clause.congruences:
        if (x*p[0]+y*p[1]-residue) % modulus:
            return False
    for x, y, colour in clause.stencil:
        q = (p[0]+x, p[1]+y)
        if board.get(q, tile[q[1] % len(tile)][q[0] % len(tile[0])]) != colour:
            return False
    return True


def direct_run(rule, tile, defects, start, heading, clauses, limit):
    board = dict(defects)
    visited = set()
    p = start
    h = heading
    matches = [None] * len(clauses)
    history = []
    for t in range(limit+1):
        history.append((p, h, tuple(direct_clause(c, p, h, board, tile) for c in clauses)))
        for j, value in enumerate(history[-1][2]):
            if value and matches[j] is None:
                matches[j] = t
        if p in visited:
            return t, matches, history
        visited.add(p)
        colour = board.get(p, tile[p[1] % len(tile)][p[0] % len(tile[0])])
        board[p] = (colour+1) % len(rule)
        h = (h + (1 if rule[colour] == 'R' else -1)) % 4
        step = ((0, 1), (1, 0), (0, -1), (-1, 0))[h]
        p = (p[0]+step[0], p[1]+step[1])
    return None, matches, history


class IndependentChecks(unittest.TestCase):
    def test_exhaustive_atoms_and_sampled_intersections(self):
        specs = list(itertools.product(range(-2, 5), (None, -1, 0, 3, 8), range(-3, 4), range(1, 7)))
        for spec in specs:
            a = ob.indices(*spec)
            truth = [n for n in range(40) if direct_atom(n, spec)]
            self.assertEqual(a.minimum(), min(truth, default=None), spec)
            self.assertEqual(a.count(-20, 39), len(truth), spec)
            for n in (-3, 0, 1, 2, 7, 8, 9, 39):
                self.assertEqual(a.contains(n), direct_atom(n, spec), (n, spec))
        rng = random.Random(81279123)
        for _ in range(8000):
            a, b = rng.sample(specs, 2)
            intersection = ob.indices(*a) & ob.indices(*b)
            end = max(a[0], b[0], a[1] or 0, b[1] or 0, 0) + lcm(a[3], b[3])
            truth = [n for n in range(end+1) if direct_atom(n, a) and direct_atom(n, b)]
            self.assertEqual(intersection.minimum(), min(truth, default=None), (a, b))
        print('INDEPENDENT atoms', len(specs), 'CRT intersections', 8000)

    def test_boolean_truth_table_compilation(self):
        rng = random.Random(315491)
        for case in range(350):
            specs = [(rng.randrange(-2, 12), rng.choice((None, rng.randrange(20))),
                      rng.randrange(-8, 9), rng.randrange(1, 7)) for _ in range(4)]
            accepted = {bits for bits in range(16) if rng.randrange(2)}
            leaves = [ob.indices(*spec) for spec in specs]
            expression = ob.empty()
            for bits in accepted:
                clause = ob.universe()
                for j, leaf in enumerate(leaves):
                    clause = clause & (leaf if bits & (1 << j) else ~leaf)
                expression = expression | clause
            boundary = max([0] + [max(s[0], 0 if s[1] is None else s[1]+1) for s in specs])
            period = lcm(*(s[3] for s in specs))
            end = boundary + period
            truth = []
            for n in range(end):
                bits = sum(1 << j for j, spec in enumerate(specs) if direct_atom(n, spec))
                if bits in accepted:
                    truth.append(n)
                self.assertEqual(expression.contains(n), bits in accepted)
            self.assertEqual(expression.minimum(), min(truth, default=None), (case, specs, accepted))
            self.assertEqual(expression.count(0, end-1), len(truth))
            for _ in range(3):
                lo, hi = sorted((rng.randrange(-4, end), rng.randrange(-4, end)))
                expected = sum(lo <= n <= hi for n in truth)
                self.assertEqual(expression.count(lo, hi), expected)
        print('INDEPENDENT arbitrary Boolean truth tables', 350)

    def test_stratified_lane_projection(self):
        rng = random.Random(7839381)
        counts = [0, 0, 0]
        for case in range(18000):
            rank = case % 3
            p = tuple(rng.randrange(-12, 13) for _ in range(2))
            q = tuple(rng.randrange(-12, 13) for _ in range(2))
            if rank == 0:
                da = db = (0, 0)
                if case % 2:
                    q = p
            elif rank == 1:
                direction = rng.choice(((1, 0), (0, -1), (-2, 1), (3, 2)))
                sa, sb = rng.randrange(-4, 5), rng.randrange(-4, 5)
                if sa == sb == 0:
                    sa = 1
                da, db = tuple(sa*x for x in direction), tuple(sb*x for x in direction)
                if case % 2:
                    offset = rng.randrange(-15, 16)
                    q = tuple(p[i]+offset*direction[i] for i in range(2))
            else:
                while True:
                    da = tuple(rng.randrange(-4, 5) for _ in range(2))
                    db = tuple(rng.randrange(-4, 5) for _ in range(2))
                    if da[0]*db[1] != da[1]*db[0]:
                        break
                if case % 2:
                    n, k = rng.randrange(30), rng.randrange(30)
                    q = tuple(p[i]+n*da[i]-k*db[i] for i in range(2))
            a = Lane(p, da, rng.randrange(-20, 21), rng.randrange(1, 9),
                     None if case % 4 == 0 else rng.randrange(40))
            b = Lane(q, db, rng.randrange(-20, 21), rng.randrange(1, 9),
                     None if case % 5 == 0 else rng.randrange(40))
            for chronology in (False, True):
                result = ob.relation_indices(a, b, chronology)
                truth = []
                for n in list(range(65)) + [10**100, 10**100+1, 10**100+2]:
                    expected = direct_relation(a, b, n, chronology)
                    self.assertEqual(result.contains(n), expected, (rank, a, b, n, chronology))
                    if n < 65 and expected:
                        truth.append(n)
                if a.last is not None:
                    self.assertEqual(result.minimum(), min(truth, default=None), (a, b, chronology))
                elif truth:
                    self.assertEqual(result.minimum(), truth[0], (a, b, chronology))
                self.assertEqual(result.count(0, 64), len(truth), (a, b, chronology))
            counts[rank] += 1
        print('INDEPENDENT lane pairs by rank', counts, 'membership comparisons', 18000*2*68)

    def check_run(self, rule, tile, defects, start, heading, clauses, limit=500):
        result = ob.decide(rule, tile, defects, start, heading)
        hits = [ob.first_hit(result, rule, tile, defects, (c,)) for c in clauses]
        maximum_hit = max((h.time for h in hits if h is not None and h.time < 5000), default=0)
        limit = max(limit, maximum_hit)
        repeat, expected, history = direct_run(rule, tile, defects, start, heading, clauses, limit)
        self.assertEqual(None if result.repeat is None or result.repeat[0] > limit else result.repeat[0], repeat)
        for j, hit in enumerate(hits):
            if repeat is not None or expected[j] is not None:
                self.assertEqual(None if hit is None else hit.time, expected[j],
                                 (rule, tile, defects, start, heading, clauses[j]))
            else:
                self.assertTrue(hit is None or hit.time >= len(history))
            if hit is not None and hit.time < len(history):
                self.assertEqual((hit.position, hit.heading), history[hit.time][:2])
        expected_union = min((x for x in expected if x is not None), default=None)
        joint = ob.first_hit(result, rule, tile, defects, clauses)
        if repeat is not None or expected_union is not None:
            self.assertEqual(None if joint is None else joint.time, expected_union)
        if joint is not None:
            self.assertTrue(0 <= joint.clause_index < len(clauses))
        # Check every represented observed time, independently of a first-hit answer.
        for lane in result.lanes:
            compiled = [ob.clause_indices(lane, c, result, rule, tile, defects) for c in clauses]
            for n in range(12):
                t = lane.t+n*lane.period
                if (lane.last is None or n <= lane.last) and t < len(history):
                    self.assertEqual(lane.point(n), history[t][0])
                    self.assertEqual(tuple(c.contains(n) for c in compiled), history[t][2])

    def test_complete_queries_separate_evolving_board(self):
        cases = 0
        # All constant one-cell rules up to palette size three, with/without defects.
        for m in range(1, 4):
            for rule in map(''.join, itertools.product('LR', repeat=m)):
                for initial in range(m):
                    for heading in range(4):
                        defects = {} if heading % 2 else {(0, 0): (initial+1) % m, (2, -1): m-1}
                        clauses = [ob.Clause(), ob.Clause(headings=()), ob.Clause(sites=())]
                        clauses += [ob.Clause(stencil=((0, 0, c),)) for c in range(m)]
                        clauses += [ob.Clause(stencil=((-1, 0, c), (0, 1, c))) for c in range(m)]
                        clauses += [ob.Clause(headings=(heading,), sites=((0, 0),), stencil=((0, 0, (initial+1) % m),))]
                        self.check_run(rule, [[initial]], defects, (0, 0), heading, clauses, 80)
                        cases += 1
        rng = random.Random(554101)
        for case in range(220):
            m = rng.randrange(1, 5)
            rule = ''.join(rng.choice('LR') for _ in range(m))
            u, v = rng.randrange(1, 4), rng.randrange(1, 4)
            tile = [[rng.randrange(m) for _ in range(u)] for _ in range(v)]
            defects = {(rng.randrange(-8, 9), rng.randrange(-8, 9)): rng.randrange(m) for _ in range(5)}
            start = (rng.randrange(-3, 4), rng.randrange(-3, 4))
            heading = rng.randrange(4)
            clauses = []
            for _ in range(4):
                clauses.append(ob.Clause(
                    headings=rng.choice((None, (), (0,), (0, 1, 2, 3))),
                    congruences=tuple((rng.randrange(-3, 4), rng.randrange(-3, 4),
                                       rng.randrange(-5, 6), rng.randrange(1, 9)) for _ in range(rng.randrange(3))),
                    sites=None if rng.randrange(4) else (start, (start[0]+1, start[1])),
                    stencil=tuple((rng.randrange(-3, 4), rng.randrange(-3, 4), rng.randrange(m)) for _ in range(rng.randrange(4)))))
            self.check_run(rule, tile, defects, start, heading, clauses)
            cases += 1
        print('INDEPENDENT evolving-board runs', cases)

    def test_huge_exact_arithmetic_and_chronology(self):
        n = 10**250+123
        all_but_zero = ~ob.indices(0, 0)
        self.assertEqual((all_but_zero & ob.indices(residue=0, modulus=n)).minimum(), n)
        self.assertEqual((ob.indices(residue=-1, modulus=n) & ob.indices(residue=-1, modulus=n+1)).minimum(), n*(n+1)-1)
        evens, odds = ob.indices(residue=0, modulus=2), ob.indices(residue=1, modulus=2)
        self.assertIsNone((~(evens | odds)).minimum())
        self.assertIsNone((ob.indices(0, n, 0, n+1) & all_but_zero).minimum())
        self.assertEqual((ob.indices(0, n+1, 0, n+1) & all_but_zero).minimum(), n+1)
        for step in (-7, 7):
            a = Lane((0, 0), (step, step), 0, 2, None)
            b = Lane((step*n, step*n), (0, 0), 2*n, 1, 0)
            self.assertIsNone(ob.relation_indices(a, b, True).minimum())
            self.assertEqual(ob.relation_indices(a, b, False).minimum(), n)
            b = Lane(b.p, b.d, 2*n-1, 1, 0)
            self.assertEqual(ob.relation_indices(a, b, True).minimum(), n)
        # Negative-direction checkerboard drift with a huge absolute-position query.
        for heading, target in ((0, (n, n)), (2, (-n, -n))):
            _, hit = ob.solve('RL', [[0, 1], [1, 0]], heading=heading,
                              clauses=(ob.Clause(sites=(target,)),))
            self.assertEqual(hit.time, 2*n)
            self.assertEqual(hit.position, target)
        result, hit = ob.solve('RL', [[0, 1], [1, 0]], {(n, n): 1},
                               clauses=(ob.Clause(sites=((n-1, n-1),), headings=(2,), stencil=((0, 0, 1),)),))
        self.assertEqual(hit.time, 2*n+2)
        self.assertEqual(hit.time, result.repeat[0])
        print('INDEPENDENT huge values: 251-digit endpoints and 501-digit CRT product')

    def test_invalid_inputs_and_optimized_guards(self):
        calls = [lambda: ob.indices(modulus=0), lambda: ob.indices(lo=0.5),
                 lambda: ob.indices(hi=1.5), lambda: ob.linear_congruence(2, 1, -1),
                 lambda: ob.Progression(0, 1, 2), lambda: ob.Progression(1, 1, 2),
                 lambda: ob.IndexSet({}), lambda: ob.indices().contains(0.5),
                 lambda: ob.indices().count(0, 2.5),
                 lambda: ob.relation_indices(Lane((0, 0), (0, 0), 0, 0, None), Lane((0, 0), (0, 0), 0, 1, 0)),
                 lambda: ob.solve('', [[0]]), lambda: ob.solve('L', [[-1]]),
                 lambda: ob.solve('L', [[0]], heading=-1),
                 lambda: ob.solve('L', [[0]], start=(0.0, 0)),
                 lambda: ob.solve('L', [[0]], {(0, 0): 1}),
                 lambda: ob.solve('L', [[0]], clauses=(ob.Clause(congruences=((1, 1, 0, 0),)),)),
                 lambda: ob.solve('L', [[0]], clauses=(ob.Clause(stencil=((0, 0, -1),)),))]
        for operation in calls:
            with self.assertRaises(ValueError):
                operation()
        print('INDEPENDENT explicit invalid-input guards', len(calls))

    def test_iterator_clause_regression_and_snapshot(self):
        fields = [('stencil', ((0, 0, 1),)),
                  ('congruences', ((1, 0, 1, 2),)),
                  ('headings', (1,)), ('sites', ((1, 0),))]
        for field, value in fields:
            prepared = iter(value) if field == 'headings' else (iter(item) for item in value)
            clause = ob.Clause(**{field: prepared})
            self.assertEqual(getattr(clause, field), value)
            for _ in range(3):
                result, hit = ob.solve('RL', [[0, 1], [1, 0]], clauses=(clause,))
                self.assertEqual(hit.time, 1, field)
                repeated = ob.first_hit(result, 'RL', [[0, 1], [1, 0]], {}, (clause,))
                self.assertEqual(repeated.time, 1, field)
        # The frozen value must not retain mutable nested user containers.
        source = [[0, 0, 1]]
        clause = ob.Clause(stencil=source)
        source[0][2] = 0
        self.assertEqual(clause.stencil, ((0, 0, 1),))
        for kwargs in ({'headings': 1}, {'sites': (1,)}, {'stencil': None}, {'congruences': (1,)}):
            with self.assertRaises(ValueError):
                ob.Clause(**kwargs)
        print('INDEPENDENT iterator normalization: four fields, nested iterators, repeated queries, immutable snapshot')


if __name__ == '__main__':
    unittest.main(verbosity=2)
