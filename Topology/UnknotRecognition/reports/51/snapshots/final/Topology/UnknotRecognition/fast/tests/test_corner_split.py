"""Compare transported complete spaces and resulting searches with fresh solves."""
import copy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank
from fastunknot.corner_split import canonical_binary_span, corner_endomorphism_space
from fastunknot.geometry import ScanLimit
from fastunknot.scalar_split import (FittingScan, binary_nullspace,
    fitting_khovanov_rank, scalar_endomorphism_space)
from primary_research.families import two_field_scan
from test_scalar_split import mixed_copies, verify_witness

ROOT = Path(__file__).resolve().parents[1]


class CornerSplitTests(unittest.TestCase):
    def test_canonical_span_matches_fresh_nullspace_and_ignores_generator_order(self):
        rng = random.Random(26100873)
        for _ in range(200):
            width = rng.randrange(1, 35)
            equations = [rng.randrange(1 << width) for _ in range(rng.randrange(40))]
            basis = binary_nullspace(equations, width)
            generators = list(basis)
            for _ in range(10):
                vector = 0
                for item in basis:
                    if rng.randrange(2):
                        vector ^= item
                generators.append(vector)
            rng.shuffle(generators)
            self.assertEqual(canonical_binary_span(generators), basis)

    def test_every_child_space_equals_fresh_solve_and_keeps_candidate_sequence(self):
        audited = 0
        def checked(*args, **kwargs):
            nonlocal audited
            actual = corner_endomorphism_space(*args, **kwargs)
            _, _, scan, group = args
            expected = scalar_endomorphism_space(scan, group, max_variables=None,
                check=kwargs.get('check'), preserve_grading=kwargs['preserve_grading'])
            self.assertEqual(actual[:3], expected[:3])
            self.assertEqual(actual[3], 0)
            audited += 1
            return actual
        factories = [(lambda r=r, **kw: two_field_scan(r, mixing='dense', **kw)[0])
                     for r in (3, 4, 6, 8, 10)]
        factories += [(lambda n=n, **kw: mixed_copies(FittingScan, n, **kw))
                      for n in (2, 3, 6)]
        for factory in factories:
            for primary in (False, True):
                direct = factory(fitting_primary=primary, record_witnesses=True)
                reused = factory(fitting_primary=primary, fitting_reuse_commutant=True,
                                 record_witnesses=True)
                direct._compress([0] * direct.live)
                with patch('fastunknot.corner_split.corner_endomorphism_space', side_effect=checked):
                    reused._compress([0] * reused.live)
                self.assertEqual((direct.mid, direct.deg, direct.out, direct.weights),
                                 (reused.mid, reused.deg, reused.out, reused.weights))
                self.assertEqual(direct.fitting_witnesses, reused.fitting_witnesses)
                self.assertEqual(direct.stats['fitting_candidates'], reused.stats['fitting_candidates'])
                self.assertLessEqual(reused.stats['fitting_commutant_builds'],
                                     direct.stats['fitting_commutant_builds'])
                for witness in reused.fitting_witnesses:
                    self.assertTrue(verify_witness(witness))
                reused.check_d_squared()
        self.assertGreater(audited, 20)

    def test_real_scans_invalidate_spaces_at_each_crossing_and_agree_with_reference(self):
        total_reuses = 0
        for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36'):
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name+'.json')).read_text()))
            expected = khovanov_rank(diagram.pd)
            direct = fitting_khovanov_rank(diagram.pd, fitting_primary=True,
                                          record_witnesses=True)
            reused = fitting_khovanov_rank(diagram.pd, fitting_primary=True,
                fitting_reuse_commutant=True, record_witnesses=True, check_d_squared=True)
            self.assertEqual(reused['by_degree'], expected['by_degree'])
            self.assertEqual(reused['witnesses'], direct['witnesses'])
            self.assertEqual(reused['stats']['fitting_candidates'], direct['stats']['fitting_candidates'])
            total_reuses += reused['stats']['fitting_corner_reuses']
        self.assertGreater(total_reuses, 0)

    def test_cache_caps_and_interrupted_transport_preserve_valid_state(self):
        options = dict(fitting_primary=True, fitting_reuse_commutant=True)
        scan, _ = two_field_scan(8, mixing='dense', **options)
        scan._compress([0] * scan.live)
        cached, _ = two_field_scan(8, mixing='dense', **options)
        cached.scalar_cache = dict(scan.scalar_cache)
        with patch('fastunknot.corner_split.corner_endomorphism_space',
                   side_effect=AssertionError('a cache hit should not transport a space')):
            cached._compress([0] * cached.live)
        self.assertEqual(cached.out, scan.out)
        self.assertEqual(cached.stats['fitting_commutant_builds'], 0)
        limited, _ = two_field_scan(8, mixing='dense', fitting_max_splits=1, **options)
        with patch('fastunknot.corner_split.corner_endomorphism_space',
                   side_effect=AssertionError('split budget must precede transport')):
            limited._compress([0] * limited.live)
        interrupted, _ = two_field_scan(8, mixing='dense', **options)
        original = copy.deepcopy((interrupted.mid, interrupted.deg, interrupted.out, interrupted.inc))
        def stop(*args, **kwargs):
            calls = 0
            def check():
                nonlocal calls
                calls += 1
                if calls == 10:
                    raise ScanLimit('interrupt inside corner transport')
            return corner_endomorphism_space(*args, **dict(kwargs, check=check))
        with patch('fastunknot.corner_split.corner_endomorphism_space', side_effect=stop):
            with self.assertRaises(ScanLimit):
                interrupted._compress([0] * interrupted.live)
        self.assertEqual((interrupted.mid, interrupted.deg, interrupted.out, interrupted.inc), original)
        interrupted._compress([0] * interrupted.live)
        self.assertEqual(interrupted.out, scan.out)
        for bad in (0, 1, None, 'yes'):
            with self.assertRaises(ValueError):
                fitting_khovanov_rank([], fitting_reuse_commutant=bad)


if __name__ == '__main__':
    unittest.main()
