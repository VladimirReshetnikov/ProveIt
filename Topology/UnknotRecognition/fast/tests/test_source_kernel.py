"""Independent rank/support checks for reusable positive source descent."""
from dataclasses import FrozenInstanceError
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations
from math import gcd, lcm
import random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot import source_kernel as module
from fastunknot.source_kernel import SourceKernel


def source(n, equations=(), conflicts=()):
    return SimpleNamespace(n=n, equations=equations, conflicts=conflicts)


def reverse_echelon(rows, n):
    """Independent elimination: rightmost pivots, no producer imports."""
    pivots = {}
    for row in rows:
        row = list(map(Q, row))
        for j in range(n-1, -1, -1):
            if not row[j]:
                continue
            if j in pivots:
                scale = row[j]
                row = [a-scale*b for a, b in zip(row, pivots[j])]
            else:
                scale = row[j]
                pivots[j] = tuple(a/scale for a in row)
                break
    return pivots


def independent_rays(s):
    answer = set()
    for size in range(1, s.n+1):
        for support in combinations(range(s.n), size):
            if any(a in support and b in support for a, b in s.conflicts):
                continue
            pivots = reverse_echelon((tuple(row[j] for j in support) for row in s.equations), size)
            if len(pivots) != size-1:
                continue
            free = next(j for j in range(size) if j not in pivots)
            x = [Q(0)]*size
            x[free] = Q(1)
            for j in sorted(pivots):
                x[j] = -sum((pivots[j][k]*x[k] for k in range(j)), Q(0))
            if not all(a > 0 for a in x):
                continue
            denominator = lcm(*(a.denominator for a in x))
            x = [int(a*denominator) for a in x]
            divisor = reduce(gcd, x)
            full = [0]*s.n
            for j, a in zip(support, x):
                full[j] = a//divisor
            answer.add(tuple(full))
    return answer


class SourceKernelTests(unittest.TestCase):
    def assertWitness(self, s, initial, c, result):
        x = result['coordinates']
        self.assertEqual(len(x), s.n)
        self.assertTrue(all(type(a) is int and a >= 0 for a in x))
        self.assertEqual(reduce(gcd, x), 1)
        self.assertTrue(all(not a or b for a, b in zip(x, initial)))
        self.assertTrue(all(sum(a*b for a, b in zip(row, x)) == 0 for row in s.equations))
        self.assertTrue(all(not (x[a] and x[b]) for a, b in s.conflicts))
        self.assertGreater(sum(a*b for a, b in zip(c, x)), 0)
        support = tuple(j for j, a in enumerate(x) if a)
        rank = len(reverse_echelon((tuple(row[j] for j in support) for row in s.equations), len(support)))
        self.assertEqual(rank, len(support)-1)
        self.assertLessEqual(result['descent_steps'], result['initial_direction_dimension'])
        self.assertLessEqual(result['initial_direction_dimension'], result['nullity']-1)
        self.assertGreaterEqual(sum(a*b for a, b in zip(c, x))/Q(sum(x)),
                                sum(a*b for a, b in zip(c, initial))/Q(sum(initial)))

    def test_random_compatible_mixtures_against_independent_rays(self):
        rng = random.Random(1180122026)
        queries = 0
        models = 0
        while queries < 600:
            n = rng.randrange(1, 8)
            rows = tuple(tuple(rng.randrange(-2, 3) for _ in range(n))
                         for _ in range(rng.randrange(n)))
            conflicts = tuple(p for p in combinations(range(n), 2) if rng.random() < .1)
            s = source(n, rows, conflicts)
            rays = sorted(independent_rays(s))
            models += 1
            if not rays:
                continue
            prepared = SourceKernel(s)
            for _ in range(min(3, 600-queries)):
                initial = list(map(Q, rng.choice(rays)))
                for ray in rng.sample(rays, min(len(rays), 4)):
                    scale = Q(rng.randrange(1, 9), rng.randrange(1, 9))
                    candidate = [a+scale*b for a, b in zip(initial, ray)]
                    if all(not (candidate[a] and candidate[b]) for a, b in conflicts):
                        initial = candidate
                c = [rng.randrange(-4, 5) for _ in range(n)]
                while sum(a*b for a, b in zip(c, initial)) <= 0:
                    c = [a+1 for a in c]
                zeros = tuple(j for j, a in enumerate(initial) if not a)
                result = prepared.extreme_witness(initial, c, zeros=zeros)
                self.assertIn(result['coordinates'], rays)
                self.assertWitness(s, initial, c, result)
                queries += 1
        self.assertEqual(queries, 600)
        self.assertLess(models, 1000)

    def test_rank_one_charts_match_fresh_constraint_spaces(self):
        rng = random.Random(11812)
        restrictions = 0
        for width in range(1, 9):
            for _ in range(20):
                constraints = [tuple(Q(rng.randrange(-3, 4), rng.randrange(1, 4))
                                     for _ in range(width))]
                basis, free = module._chart(constraints, width, lambda: None)
                for step in range(width+3):
                    # Duplicate and zero rows force dependent restrictions too.
                    row = constraints[-1] if step % 3 == 0 else tuple(
                        Q(rng.randrange(-3, 4), rng.randrange(1, 4)) for _ in range(width))
                    if step % 4 == 0:
                        row = (Q(0),)*width
                    basis, free = module._restrict_chart(basis, free, row, lambda: None)
                    constraints.append(row)
                    expected_dimension = width-len(reverse_echelon(constraints, width))
                    self.assertEqual(len(basis), expected_dimension)
                    self.assertEqual(len(free), expected_dimension)
                    for i, vector in enumerate(basis):
                        self.assertEqual(tuple(vector[j] for j in free),
                                         tuple(int(i == j) for j in range(len(free))))
                        self.assertTrue(all(sum(a*b for a, b in zip(row, vector)) == 0
                                            for row in constraints))
                    restrictions += 1
        self.assertEqual(restrictions, 1200)

    def test_dependent_simultaneous_zeros_and_reused_kernel(self):
        s = source(5, ((1, -1, 0, 0, 0), (0, 0, 1, -1, 0)))
        prepared = SourceKernel(s)
        restrictions = []
        original = module._restrict_chart
        def record(basis, free, form, check):
            result = original(basis, free, form, check)
            restrictions.append((len(basis), len(result[0])))
            return result
        with patch.object(module, '_restrict_chart', record):
            result = prepared.extreme_witness((1, 1, 2, 2, 1), (1, 1, 1, 1, 4))
        self.assertWitness(s, (1, 1, 2, 2, 1), (1, 1, 1, 1, 4), result)
        self.assertEqual(result['coordinates'], (0, 0, 0, 0, 1))
        self.assertTrue(any(a == b for a, b in restrictions))
        with patch.object(module, '_chart', wraps=module._chart) as kernel:
            again = prepared.extreme_witness((0, 0, 1, 1, 0), (1,)*5, zeros=(0, 1, 4))
        self.assertEqual(kernel.call_count, 1)
        self.assertEqual(again['descent_steps'], 0)

    def test_objective_orientation_and_large_rational_input(self):
        s = source(3)
        prepared = SourceKernel(s)
        result = prepared.extreme_witness((1, 1, 1), (5, -1, -1))
        self.assertEqual(result['coordinates'], (1, 0, 0))
        self.assertWitness(s, (1, 1, 1), (5, -1, -1), result)
        a = 2**301+3
        denominator = 2**1024+1
        s = source(4, ((1, -a, 0, 0),))
        initial = (Q(a, denominator), Q(1, denominator), Q(3, 7), Q(2, 11))
        c = (Q(1, a), 1, 3, 7)
        result = SourceKernel(s).extreme_witness(initial, c)
        self.assertWitness(s, initial, c, result)
        self.assertIn(result['coordinates'], independent_rays(s))

    def test_snapshot_is_immutable(self):
        rows = [[1, -1, 0]]
        conflicts = [[0, 2]]
        s = source(3, rows, conflicts)
        prepared = SourceKernel(s)
        rows[0][0] = 9
        conflicts[0][1] = 1
        s.n = 8
        self.assertEqual(prepared.n, 3)
        self.assertEqual(prepared.equations, ((1, -1, 0),))
        self.assertEqual(prepared.conflicts, ((0, 2),))
        self.assertEqual(prepared.extreme_witness((2, 2, 0), (1, 1, 0))['coordinates'], (1, 1, 0))
        with self.assertRaises(FrozenInstanceError):
            prepared.n = 4

    def test_source_and_query_validation(self):
        for s in (source(True), source(0), source(2, ((1,),)), source(1, ((True,),)),
                  source(1, ((1.0,),)), source(2, (), ((0, 0),)),
                  source(2, (), ((0, True),)), source(2, (), ((0, 2),)), object(),
                  source(1, (('1/0',),)), source(2, ('11',)),
                  source(2, ({0: 1, 1: -1},)), source(2, (), ({0, 1},))):
            with self.assertRaises(ValueError):
                SourceKernel(s)
        prepared = SourceKernel(source(3, ((1, -1, 0),), ((0, 2),)))
        cases = [((0, 0, 0), (1,)*3, ()), ((-1, -1, 0), (1,)*3, ()),
                 ((1, 2, 0), (1,)*3, ()), ((1, 1, 1), (1,)*3, ()),
                 ((1, 1, 0), (-1,)*3, ()), ((1, 1, 0), (1,), ()),
                 ((1, 1), (1,)*3, ()), ((1.0, 1, 0), (1,)*3, ()),
                 ((1, 1, 0), (True, 1, 1), ()), ((1, 1, 0), (1,)*3, (0,)),
                 ((1, 1, 0), (1,)*3, (True,)), ((1, 1, 0), (1,)*3, (-1,)),
                 ('110', (1,)*3, ()), ((1, 1, 0), '111', ()),
                 ((1, 1, 0), (1,)*3, {2: True}), ((1, 1, 0), (1,)*3, '2'),
                 ((1, 1, '1/0'), (1,)*3, ()), ({0: 1, 1: 1, 2: 0}, (1,)*3, ()),
                 ((1, 1, 0), {0, 1, 2}, ())]
        for x, c, zeros in cases:
            with self.subTest(x=x, c=c, zeros=zeros), self.assertRaises(ValueError):
                prepared.extreme_witness(x, c, zeros=zeros)
        with self.assertRaises(ValueError):
            SourceKernel(source(1, ((1,),))).extreme_witness((1,), (1,))
        self.assertEqual(prepared.extreme_witness((1, 1, 0), (1,)*3, zeros={2})['coordinates'], (1, 1, 0))

    def test_callbacks_propagate_even_when_falsey_or_named_like_validation(self):
        class Callback:
            def __init__(self, after, error):
                self.after, self.error, self.calls = after, error, 0
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.after:
                    raise self.error
        for error in (ValueError('external'), TypeError('external'), RuntimeError('external')):
            callback = Callback(1, error)
            with self.assertRaises(type(error)) as caught:
                SourceKernel(source(3), check=callback)
            self.assertIs(caught.exception, error)
            prepared = SourceKernel(source(4))
            for after in (1, 12, 25):
                callback = Callback(after, error)
                with self.assertRaises(type(error)) as caught:
                    prepared.extreme_witness((1,)*4, (1,)*4, check=callback)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
