from __future__ import annotations
import itertools
import random
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from component_kernel import (ComponentPlan, ComponentAlgebra, KernelLimit,
                              pack, support, subset_convolution)
from reference_planar import ReferencePlanar, brute, component, matchings
from fixtures import zipper_triple

COUNTS = {"convolution_pairs": 0, "matching_compositions": 0,
          "matching_triples": 0, "positive_genus_plans": 0,
          "general_plans": 0, "general_compositions": 0, "zipper_triples": 0,
          "associativity_checks": 0, "adapter_compositions": 0}


class ConvolutionTests(unittest.TestCase):
    def test_exhaustive_k_up_to_three(self):
        for k in range(4):
            n = 1 << k
            for f in range(1 << n):
                a = [(f >> s) & 1 for s in range(n)]
                for g in range(1 << n):
                    b = [(g >> s) & 1 for s in range(n)]
                    expected = [0] * n
                    for s in range(n):
                        t = s
                        while True:
                            expected[s] ^= a[t] & b[s ^ t]
                            if t == 0:
                                break
                            t = (t - 1) & s
                    self.assertEqual(list(subset_convolution(a, b, k)), expected)
                    COUNTS['convolution_pairs'] += 1

    def test_random_larger_and_square_identity(self):
        rng = random.Random(91871)
        for k in range(4, 11):
            n = 1 << k
            for _ in range(12):
                f, g = rng.getrandbits(n), rng.getrandbits(n)
                a = [(f >> s) & 1 for s in range(n)]
                b = [(g >> s) & 1 for s in range(n)]
                result = subset_convolution(a, b, k)
                for s in range(n):
                    t, v = s, 0
                    while True:
                        v ^= a[t] & b[s ^ t]
                        if not t:
                            break
                        t = (t - 1) & s
                    self.assertEqual(result[s], v)
                self.assertEqual(pack(subset_convolution(a, a, k)), f & 1)
                COUNTS['convolution_pairs'] += 2

    def test_bit_serialization(self):
        rng = random.Random(166)
        for n in (0, 1, 8, 17, 255, 1024, 10001):
            f = rng.getrandbits(n)
            arr = [(f >> j) & 1 for j in range(n)]
            self.assertEqual(pack(arr), f)
            self.assertEqual(list(support(f)), [i for i, v in enumerate(arr) if v])

    def test_reject_invalid(self):
        for args in (([0], [0], -1), ([0], [0], 1), ([2], [0], 0)):
            with self.assertRaises(ValueError):
                subset_convolution(*args)


class CompositionTests(unittest.TestCase):
    def test_exhaustive_small_matching_algebras(self):
        # All coefficients, all planar triples through six boundary points.
        for m in range(4):
            ref = ReferencePlanar()
            ids = [ref.intern(x) for x in matchings(tuple(range(2 * m)))]
            for a, b, c in itertools.product(ids, repeat=3):
                plan = ref.compose_plan(a, b, c)
                COUNTS['matching_triples'] += 1
                if plan is None:
                    COUNTS['positive_genus_plans'] += 1
                    self.assertEqual(ref.compose(a, b, c, 1, 1), 0)
                    continue
                fast = ComponentPlan(plan[0])
                r, s = fast.dim.left, fast.dim.right
                for f in range(1 << (1 << r)):
                    for g in range(1 << (1 << s)):
                        self.assertEqual(fast.compose(f, g), ref.compose(a, b, c, f, g),
                                         (m, a, b, c, f, g))
                        COUNTS['matching_compositions'] += 1

    def test_explicit_zipper_family(self):
        for d in range(1, 9):
            for blocks in range(1, 4):
                ref = ReferencePlanar()
                a, b, c = map(ref.intern, zipper_triple(d, blocks))
                plan = ref.compose_plan(a, b, c)
                self.assertIsNotNone(plan)
                rows = plan[0]
                self.assertEqual(len(rows), blocks)
                expected = tuple(component(((1 << d) - 1) << (j*d),
                                           ((1 << d) - 1) << (j*d), 1 << j, 0)
                                 for j in range(blocks))
                self.assertEqual(rows, expected)
                r, s, t = [ref.basis(x, y)[1] for x, y in ((a,b), (b,c), (a,c))]
                self.assertEqual((r, s, t), (d*blocks, d*blocks, blocks))
                self.assertEqual(r+s+t-len(ref.pairs[b]), 2*blocks)
                COUNTS['zipper_triples'] += 1

    def test_random_matching_triples(self):
        rng = random.Random(554321)
        for m in range(4, 8):
            ref = ReferencePlanar()
            ids = [ref.intern(x) for x in matchings(tuple(range(2 * m)))]
            for _ in range(600):
                a, b, c = (rng.choice(ids) for _ in range(3))
                plan = ref.compose_plan(a, b, c)
                COUNTS['matching_triples'] += 1
                if plan is None:
                    COUNTS['positive_genus_plans'] += 1
                    continue
                fast = ComponentPlan(plan[0])
                for _ in range(4):
                    f = rng.getrandbits(1 << fast.dim.left)
                    g = rng.getrandbits(1 << fast.dim.right)
                    self.assertEqual(fast.compose(f, g), ref.compose(a, b, c, f, g))
                    COUNTS['matching_compositions'] += 1

    def test_general_counits_extras_and_splittings(self):
        rng = random.Random(71881)
        for _ in range(1200):
            k = rng.randrange(0, 6)
            masks = [[0, 0, 0, rng.randrange(3)] for j in range(k)]
            for side in range(3):
                n = rng.randrange(0, 6) if k else 0
                for bit in range(n):
                    masks[rng.randrange(k)][side] |= 1 << bit
            components = tuple(component(*row) for row in masks)
            fast = ComponentPlan(components)
            COUNTS['general_plans'] += 1
            for _ in range(20):
                f = rng.getrandbits(1 << fast.dim.left)
                g = rng.getrandbits(1 << fast.dim.right)
                self.assertEqual(fast.compose(f, g), brute(components, f, g))
                COUNTS['general_compositions'] += 1

    def test_associativity(self):
        rng = random.Random(17013)
        for m in range(1, 6):
            ref = ReferencePlanar()
            ids = [ref.intern(x) for x in matchings(tuple(range(2 * m)))]
            def mul(a, b, c, f, g):
                p = ref.compose_plan(a, b, c)
                return 0 if p is None else ComponentPlan(p[0]).compose(f, g)
            for _ in range(200):
                a, b, c, d = (rng.choice(ids) for _ in range(4))
                f = rng.getrandbits(1 << ref.basis(a, b)[1])
                g = rng.getrandbits(1 << ref.basis(b, c)[1])
                h = rng.getrandbits(1 << ref.basis(c, d)[1])
                self.assertEqual(mul(a, c, d, mul(a, b, c, f, g), h),
                                 mul(a, b, d, f, mul(b, c, d, g, h)))
                COUNTS['associativity_checks'] += 1

    def test_adaptive_adapter_and_stage_reset(self):
        rng = random.Random(20)
        ref = ReferencePlanar()
        a = ref.intern(tuple((2 * j, 2 * j + 1) for j in range(8)))
        adapter = ComponentAlgebra(ref, min_pairs=0)
        for _ in range(30):
            f, g = rng.getrandbits(256), rng.getrandbits(256)
            self.assertEqual(adapter.compose(a, a, a, f, g), ref.compose(a, a, a, f, g))
            COUNTS['adapter_compositions'] += 1
        self.assertGreater(adapter.kernel_stats['compressed_calls'], 0)
        adapter.stage()
        self.assertEqual(adapter.kernels, {})
        small = ComponentAlgebra(ref, max_entries=0, min_pairs=0)
        self.assertEqual(small.compose(a, a, a, f, g), ref.compose(a, a, a, f, g))
        self.assertEqual(small.kernel_stats['allocation_fallbacks'], 1)
        COUNTS['adapter_compositions'] += 1

    def test_invalid_plan_and_basis(self):
        for p in (((1, 1, 1, 0), (1, 2, 2, 0)), ((2, 1, 1, 0),),
                  ((1, -1, 1, 0),), ((1, 1, 1, 0, (5,)),)):
            with self.assertRaises(ValueError):
                ComponentPlan(p)
        p = ComponentPlan(((1, 1, 1, 0),))
        for f, g in ((-1, 1), (4, 1), (1, 4), (True, 1)):
            with self.assertRaises(ValueError):
                p.compose(f, g)
        with self.assertRaises(KernelLimit):
            ComponentPlan(((1, 1, 1, 0),), max_entries=0)

    def test_budget_callback_propagates(self):
        class Stop(RuntimeError):
            pass
        def check():
            raise Stop('cooperative budget')
        with self.assertRaises(Stop):
            ComponentPlan(((1, 1, 1, 0),), check=check)
        p = ComponentPlan(((1, 1, 1, 0),))
        p.check = check
        with self.assertRaises(Stop):
            p.compose(3, 3)
