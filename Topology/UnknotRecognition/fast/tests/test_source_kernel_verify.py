"""Independent source-coordinate oracles for the prepared ray checker."""

from dataclasses import FrozenInstanceError
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, lcm
from random import Random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.source_kernel_verify import SourceKernelVerifier


def source(n, equations=(), conflicts=()):
    return SimpleNamespace(n=n, equations=equations, conflicts=conflicts)


def rref(rows, n):
    """Test-only left-pivot full elimination, independent of checker chart."""
    a = [list(map(Q, row)) for row in rows]
    pivots = []
    for j in range(n):
        p = next((k for k in range(len(pivots), len(a)) if a[k][j]), None)
        if p is None:
            continue
        k = len(pivots)
        a[k], a[p] = a[p], a[k]
        scale = a[k][j]
        a[k] = [v/scale for v in a[k]]
        for other in range(len(a)):
            if other != k:
                scale = a[other][j]
                a[other] = [v-scale*w for v, w in zip(a[other], a[k])]
        pivots.append(j)
    return a, pivots


def primitive(x):
    denominator = lcm(*(Q(v).denominator for v in x))
    ints = [int(Q(v)*denominator) for v in x]
    divisor = gcd(*ints)
    return tuple(v//divisor for v in ints)


def oracle(s, x, c, zeros=()):
    if not any(x) or any(v < 0 for v in x) or gcd(*x) != 1:
        return False
    if any(sum(a*b for a, b in zip(row, x)) for row in s.equations):
        return False
    if any(x[a] and x[b] for a, b in s.conflicts) or any(x[j] for j in zeros):
        return False
    if sum(a*b for a, b in zip(c, x)) <= 0:
        return False
    support = [j for j, value in enumerate(x) if value]
    _, pivots = rref([[row[j] for j in support] for row in s.equations], len(support))
    return len(support)-len(pivots) == 1


def rays(s):
    answer = set()
    for mask in range(1, 1 << s.n):
        support = [j for j in range(s.n) if mask >> j & 1]
        a, pivots = rref([[row[j] for j in support] for row in s.equations], len(support))
        if len(support)-len(pivots) != 1:
            continue
        j = next(j for j in range(len(support)) if j not in pivots)
        local = [Q(0)]*len(support)
        local[j] = Q(1)
        for i, p in enumerate(pivots):
            local[p] = -a[i][j]
        if all(v < 0 for v in local):
            local = [-v for v in local]
        if any(v <= 0 for v in local):
            continue
        full = [Q(0)]*s.n
        for j, v in zip(support, local):
            full[j] = v
        full = primitive(full)
        if oracle(s, full, (1,)*s.n):
            answer.add(full)
    return answer


class PreparedRayVerifierTests(unittest.TestCase):
    def test_replay_prepares_without_producer_algebra(self):
        from fastunknot import source_kernel
        s = source(5, ((1, -1, 0, 0, 0), (0, 0, 1, -1, 0)))
        c = (1, 1, 1, 1, 4)
        packet = source_kernel.SourceKernel(s).extreme_witness((1, 1, 2, 2, 1), c)
        with patch.object(source_kernel, '_chart', side_effect=AssertionError('producer disabled')), \
                patch.object(source_kernel, '_restrict_chart', side_effect=AssertionError('producer disabled')):
            v = SourceKernelVerifier(s)
            self.assertTrue(v.verify(packet['coordinates'], c))
            self.assertTrue(v.verify((1, 1, 0, 0, 0), c))
            self.assertFalse(v.verify((1, 1, 1, 1, 0), c))

    def test_rank_criterion_and_degenerate_nullities(self):
        s = source(4, ((1, -1, 0, 0),))
        v = SourceKernelVerifier(s)
        self.assertEqual(v.nullity, 3)
        self.assertTrue(v.verify((1, 1, 0, 0), (1,)*4))
        self.assertTrue(v.verify((1, 1, 0, 0), (1,)*4, zeros=frozenset((2, 3))))
        self.assertFalse(v.verify((1, 1, 1, 1), (1,)*4))
        self.assertTrue(v.verify((0, 0, 1, 0), (1,)*4))
        line = SourceKernelVerifier(source(2, ((1, -1),)))
        self.assertEqual(line.nullity, 1)
        self.assertTrue(line.verify((1, 1), (1, 1)))
        zero = SourceKernelVerifier(source(2, ((1, 0), (0, 1))))
        self.assertEqual(zero.nullity, 0)
        self.assertFalse(zero.verify((1, 0), (1, 1)))
        self.assertFalse(zero.verify((0, 0), (1, 1)))

    def test_cache_never_authenticates_other_witness_checks(self):
        v = SourceKernelVerifier(source(3, ((1, -1, 0),)), cache_size=1)
        self.assertTrue(v.verify((1, 1, 0), (1, 1, 1)))
        self.assertFalse(v.verify((1, 2, 0), (1, 1, 1)))  # Same support; not matching.
        self.assertFalse(v.verify((2, 2, 0), (1, 1, 1)))  # Not primitive.
        self.assertFalse(v.verify((1, 1, 0), (-1, -1, 1)))
        self.assertFalse(v.verify((1, 1, 0), (1, 1, 1), zeros=(1,)))
        self.assertTrue(v.verify((0, 0, 1), (1, 1, 1)))
        self.assertEqual(len(v._support_cache), 1)
        self.assertTrue(v.verify((1, 1, 0), (1, 1, 1)))
        self.assertEqual(len(v._support_cache), 1)
        uncached = SourceKernelVerifier(source(2), cache_size=0)
        self.assertTrue(uncached.verify((1, 0), (1, 1)))
        self.assertFalse(uncached._support_cache)
        incompatible = SourceKernelVerifier(source(2, ((1, -1),), ((0, 1),)))
        self.assertFalse(incompatible.verify((1, 1), (1, 1)))

    def test_source_snapshot_and_frozen_chart(self):
        s = source(2, [[1, -1]], [])
        v = SourceKernelVerifier(s)
        s.equations[0][1] = 1
        s.conflicts.append((0, 1))
        s.n = 3
        self.assertTrue(v.verify((1, 1), (1, 1)))
        self.assertEqual(v.equations, ((1, -1),))
        with self.assertRaises(FrozenInstanceError):
            v.basis = ()

    def test_large_rational_equations_and_exact_objectives(self):
        big = 2**521+1
        s = source(3, ((Q(1, big), -1, 0), (Q(7, 3*big), Q(-7, 3), 0)))
        v = SourceKernelVerifier(s)
        self.assertTrue(v.verify((big, 1, 0), (Q(1, big), -Q(1, 2), 0)))
        self.assertTrue(v.verify((str(big), '1', '0'), ('1/'+str(big), '0', '0')))
        self.assertFalse(v.verify((big-1, 1, 0), (1, 1, 1)))
        self.assertFalse(v.verify((big, 1, 0), (Q(1, big), -1, 0)))

    def test_malformed_source_and_cache_configuration(self):
        bad = (source(True), source(0), source(2, ((1,),)), source(1, ((True,),)),
               source(1, ((1.0,),)), source(1, (('1/0',),)), source(2, (), ((0, 0),)),
               source(2, (), ((0, True),)), source(2, (), ((0, 2),)), source(2, (), ((0,),)),
               source(2, {'row': (1, -1)}), source(2, ({0: 1, 1: -1},)), object())
        for s in bad:
            with self.subTest(source=s), self.assertRaises((ValueError, TypeError)):
                SourceKernelVerifier(s)
        for size in (True, -1, Q(1), None):
            with self.assertRaises(ValueError):
                SourceKernelVerifier(source(1), cache_size=size)

    def test_malformed_witnesses(self):
        v = SourceKernelVerifier(source(2, ((1, -1),)))
        for x in ((True, 1), (1.0, 1), ('1/0', 1), (Q(1, 2), Q(1, 2)),
                  (-1, -1), (0, 0), (1,), '11', {0: 1, 1: 1}, None):
            self.assertFalse(v.verify(x, (1, 1)), x)
        for c in ((True, 1), (1.0, 1), (1,), '11', None):
            self.assertFalse(v.verify((1, 1), c), c)
        for zero in ((True,), (-1,), (2,), (Q(0),), '0', None):
            self.assertFalse(v.verify((1, 1), (1, 1), zeros=zero), zero)

    def test_callbacks_propagate_at_entry_inside_algebra_and_on_cache_hits(self):
        class Stop(ValueError):
            pass
        class Callback:
            def __init__(self, limit, error=Stop):
                self.calls, self.limit, self.error = 0, limit, error
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.limit:
                    raise self.error('external cancellation')
        for error in (Stop, ValueError, TypeError, RuntimeError):
            with self.assertRaisesRegex(error, 'external cancellation'):
                SourceKernelVerifier(source(2), check=Callback(1, error))
            v = SourceKernelVerifier(source(3, ((1, -1, 0),)))
            for limit in (1, 3, 8):
                with self.assertRaisesRegex(error, 'external cancellation'):
                    v.verify((1, 1, 0), (1, 1, 1), check=Callback(limit, error))
        with self.assertRaisesRegex(Stop, 'external cancellation'):
            SourceKernelVerifier(source(3, ((1, -1, 0),)), check=Callback(5))
        v = SourceKernelVerifier(source(3, ((1, -1, 0),)))
        self.assertTrue(v.verify((1, 1, 0), (1, 1, 1)))
        with self.assertRaisesRegex(Stop, 'external cancellation'):
            v.verify((1, 1, 0), (1, 1, 1), check=Callback(8))

    def test_random_original_coordinate_oracles(self):
        rng = Random(11820261012)
        comparisons, positive = 0, 0
        for model in range(120):
            n = 1+model % 6
            s = source(n, tuple(tuple(rng.randrange(-2, 3) for _ in range(n))
                                for _ in range(rng.randrange(n))),
                       tuple(p for p in combinations(range(n), 2) if rng.random() < .12))
            v = SourceKernelVerifier(s, cache_size=model % 5)
            expected = rays(s)
            for ray in expected:
                self.assertTrue(v.verify(ray, (1,)*n), (s, ray))
                positive += 1
                self.assertFalse(v.verify(tuple(2*x for x in ray), (1,)*n))
            candidates = list(expected)+[tuple(rng.randrange(3) for _ in range(n)) for _ in range(15)]
            for x in candidates:
                cost = tuple(rng.randrange(-2, 4) for _ in range(n))
                zeros = tuple(j for j in range(n) if rng.random() < .15)
                self.assertEqual(v.verify(x, cost, zeros=zeros), oracle(s, x, cost, zeros),
                                 (s, x, cost, zeros))
                comparisons += 1
        self.assertEqual(positive, 223)
        self.assertEqual(comparisons, 2023)


if __name__ == '__main__':
    unittest.main()
