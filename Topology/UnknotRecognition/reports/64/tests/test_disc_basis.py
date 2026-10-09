import copy
import importlib.util
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from disc_basis import (Candidate, ResourceLimit, reduce_family, exterior_feature,
                        grade, star_partition, top_pairing, validate_partition, cut_feature)
from check_certificate import verify
from reference import partitions, compatible, minor_feature, best_cost, ribbon_boundaries, forest_join, gf2_rank, mobius_homogeneous


def family(r, seed=0):
    rng = random.Random(seed)
    return [Candidate(f'p{i}', p, rng.randrange(-20, 21)) for i, p in enumerate(partitions(r))]


class DiscBasisTests(unittest.TestCase):
    def test_partition_validation(self):
        for p in [(), (1,), (0, 2), (0, True), (0, -1)]:
            with self.assertRaises(ValueError):
                validate_partition(p)
        validate_partition((0, 0, 1, 2, 1))

    def test_boolean_degree_projection(self):
        for r in range(1, 7):
            for p in partitions(r):
                self.assertEqual(mobius_homogeneous(cut_feature(p), r, grade(p)), exterior_feature(p))

    def test_small_minors(self):
        for r in range(1, 6):
            for p in partitions(r):
                self.assertEqual(exterior_feature(p), minor_feature(p))

    def test_pairing(self):
        for r in range(1, 6):
            ps = list(partitions(r))
            for p in ps:
                for q in ps:
                    self.assertEqual(top_pairing(p, q), int(compatible(p, q)))

    def test_full_matrix_rank(self):
        for r in range(1, 6):
            ps = list(partitions(r))
            rows = [sum(int(compatible(p, q)) << j for j, q in enumerate(ps)) for p in ps]
            self.assertEqual(gf2_rank(rows), 1 << (r-1))

    def test_weighted_representativity(self):
        for r in range(1, 7):
            for seed in range(4):
                cs = family(r, seed)
                kept, result = reduce_family(cs, r)
                self.assertTrue(verify([c.record() for c in cs], result['certificate']))
                for q in partitions(r):
                    self.assertEqual(best_cost(cs, q), best_cost(kept, q))

    def test_cut_baseline(self):
        cs = family(6, 80)
        ext, _ = reduce_family(cs, 6)
        cut, _ = reduce_family(cs, 6, method='cut', certificate=False)
        for q in partitions(6):
            self.assertEqual(best_cost(cs, q), best_cost(ext, q))
            self.assertEqual(best_cost(cs, q), best_cost(cut, q))

    def test_optimal_lower_bound_family(self):
        for r in range(1, 10):
            cs = [Candidate(str(a), star_partition(r, a)) for a in range(1 << (r-1))]
            kept, _ = reduce_family(cs, r)
            self.assertEqual(len(kept), len(cs))
            full = (1 << (r-1))-1
            for a in range(1 << (r-1)):
                self.assertEqual(exterior_feature(star_partition(r, a)), 1 << a)
                self.assertTrue(compatible(star_partition(r, a), star_partition(r, full ^ a)))

    def test_separate_controls(self):
        cs = family(5)
        cs += [Candidate(c.id+'B', c.partition, -100, 'B') for c in cs[:]]
        kept, result = reduce_family(cs, 5)
        self.assertEqual(len(kept), 32)
        self.assertTrue(verify([c.record() for c in cs], result['certificate']))
        for control in ('default', 'B'):
            for q in partitions(5):
                self.assertEqual(best_cost(cs, q, control), best_cost(kept, q, control))

    def test_huge_and_negative_costs(self):
        cs = [Candidate('a', (0, 1), -(1 << 16000)), Candidate('b', (0, 1), 1 << 16000)]
        kept, result = reduce_family(cs, 2)
        self.assertEqual([c.id for c in kept], ['a'])
        self.assertTrue(verify([c.record() for c in cs], result['certificate']))

    def test_empty_family_and_one_port(self):
        kept, res = reduce_family([], 3)
        self.assertEqual(kept, [])
        self.assertTrue(verify([], res['certificate']))
        kept, _ = reduce_family([Candidate('a', (0,), 2), Candidate('b', (0,), -1)], 1)
        self.assertEqual(kept[0].id, 'b')

    def test_resource_caps(self):
        with self.assertRaises(ResourceLimit):
            reduce_family([], 19)
        with self.assertRaises(ResourceLimit):
            reduce_family(family(3), 3, max_rows=2)
        with self.assertRaises(ValueError):
            reduce_family([], True)
        with self.assertRaises(ValueError):
            reduce_family([], 0)

    def test_invalid_candidates(self):
        for cs in [[Candidate('a', (0,)), Candidate('a', (0,))], [Candidate('a', (0,), True)], [Candidate('', (0,))]]:
            with self.assertRaises(ValueError):
                reduce_family(cs, 1)

    def test_source_binding_and_mutations(self):
        cs = family(5)
        _, out = reduce_family(cs, 5)
        records, cert = [c.record() for c in cs], out['certificate']
        self.assertTrue(verify(records, cert))
        changed = copy.deepcopy(records)
        changed[0]['cost_hex'] = '0x123'
        self.assertFalse(verify(changed, cert))
        for modify in ('zero', 'missing', 'duplicate', 'extra', 'r', 'boolean'):
            bad = copy.deepcopy(cert)
            if modify == 'zero': bad['dropped'][0]['xor_hex'] = '0x0'
            if modify == 'missing': bad['dropped'].pop()
            if modify == 'duplicate': bad['kept'].append(bad['kept'][0])
            if modify == 'extra': bad['unknown'] = True
            if modify == 'r': bad['r'] = 6
            if modify == 'boolean': bad['version'] = True
            self.assertFalse(verify(records, bad), modify)

    def test_checker_independence(self):
        cs = family(4)
        _, out = reduce_family(cs, 4)
        import disc_basis
        old = disc_basis.exterior_feature
        disc_basis.exterior_feature = lambda p: (_ for _ in ()).throw(AssertionError('producer disabled'))
        try:
            self.assertTrue(verify([c.record() for c in cs], out['certificate']))
        finally:
            disc_basis.exterior_feature = old

    def test_connected_not_disc(self):
        self.assertFalse(compatible((0, 0), (0, 0)))
        self.assertEqual(ribbon_boundaries([[0, 1, 2]], [[0, 1, 2]]), 1)
        self.assertEqual(ribbon_boundaries([[0, 1, 2]], [[0, 2, 1]]), 3)

    def test_not_a_counting_reduction(self):
        cs = [c for c in family(3) if grade(c.partition) == 1]
        kept, _ = reduce_family(cs, 3)
        self.assertEqual(len(kept), 2)
        self.assertTrue(any(sum(compatible(c.partition, q) for c in cs) != sum(compatible(c.partition, q) for c in kept) for q in partitions(3)))

    def test_staged_acyclic_joins(self):
        rng = random.Random(39)
        r = 5
        ps = list(partitions(r))
        full = family(r, 2)
        reduced, _ = reduce_family(full, r)
        for stage in range(3):
            patches = [(p, rng.randrange(-10, 11)) for p in rng.sample(ps, 8)]
            def apply(cs):
                out = []
                for i, c in enumerate(cs):
                    for j, (p, cost) in enumerate(patches):
                        joined = forest_join(c.partition, p)
                        if joined is not None:
                            out.append(Candidate(f'{stage}_{i}_{j}', joined, c.cost+cost))
                return out
            full = apply(full)
            reduced, _ = reduce_family(apply(reduced), r)
            for q in ps:
                self.assertEqual(best_cost(full, q), best_cost(reduced, q))


if __name__ == '__main__':
    unittest.main()
