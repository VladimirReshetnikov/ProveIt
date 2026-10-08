"""Exact coefficient factors and complete forest-substituted commutants."""
import copy
import itertools
import json
from pathlib import Path
import random
import sys
from types import SimpleNamespace
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram
from fastunknot.coefficient_span import factor_coefficients
from fastunknot.scalar_split import (FittingScan, _columns, _commutes, binary_nullspace,
    find_scalar_split, fitting_khovanov_rank, scalar_endomorphism_space)
from primary_research.families import two_field_scan


def abstract_complex(source_sizes, target_sizes, rng, coefficient_bits=4):
    blocks, mid, deg = [], [], []
    for index, size in enumerate(source_sizes + target_sizes):
        block = list(range(len(mid), len(mid) + size))
        blocks.append(block)
        mid.extend([index] * size)
        deg.extend([int(index >= len(source_sizes))] * size)
    out = [{} for _ in mid]
    for sources in blocks[:len(source_sizes)]:
        for targets in blocks[len(source_sizes):]:
            for source in sources:
                for target in targets:
                    value = rng.randrange(1 << coefficient_bits)
                    if value:
                        out[source][target] = value
    return SimpleNamespace(mid=mid, deg=deg, out=out)


class CoefficientFactorTests(unittest.TestCase):
    def test_exact_factor_reconstruction_and_independence(self):
        rng = random.Random(261008101)
        for _ in range(120):
            source_size, target_size = rng.randrange(1, 7), rng.randrange(1, 7)
            entries = [(s, t, rng.getrandbits(rng.randrange(1, 100)))
                       for s in range(source_size) for t in range(target_size)]
            values, matrices = factor_coefficients(entries, source_size, target_size)
            for source, target, original in entries:
                reconstructed = 0
                for value, matrix in zip(values, matrices):
                    if matrix[source] >> target & 1:
                        reconstructed ^= value
                self.assertEqual(reconstructed, original)
            ambient = max((value.bit_length() for value in values), default=0)
            self.assertEqual(len(values), ambient - len(binary_nullspace(values, ambient)))

    def test_invalid_factor_inputs(self):
        for entries, source_size, target_size in [([(0, 0, -1)], 1, 1),
                ([(1, 0, 1)], 1, 1), ([(0, 0, 1), (0, 0, 2)], 1, 1),
                ([], -1, 1), ([(False, 0, 1)], 1, 1)]:
            with self.assertRaises(ValueError):
                factor_coefficients(entries, source_size, target_size)


class CompleteCommutantTests(unittest.TestCase):
    def compare(self, scan, *, preserve_grading=False):
        group = list(range(len(scan.mid)))
        direct = scalar_endomorphism_space(scan, group, max_variables=None,
                                           preserve_grading=preserve_grading)
        for mode in ('span', 'forest'):
            stats = {}
            current = scalar_endomorphism_space(scan, group, max_variables=None,
                preserve_grading=preserve_grading, coefficient_mode=mode,
                coefficient_stats=stats)
            self.assertEqual(current[:3], direct[:3])
            for vector in current[2]:
                self.assertTrue(_commutes(scan, group, current[0],
                    _columns(current[0], current[1], vector)))
        return direct

    def test_exhaustive_two_by_two_two_coefficient_matrices(self):
        for entries in itertools.product(range(4), repeat=4):
            scan = SimpleNamespace(mid=[0, 0, 0, 0], deg=[0, 0, 1, 1],
                out=[{2 + target: entries[2 * source + target] for target in range(2)
                      if entries[2 * source + target]} for source in range(2)] + [{}, {}])
            self.compare(scan)

    def test_singleton_components_empty_group_and_closed_group_requirement(self):
        scan = SimpleNamespace(mid=[0, 1, 2, 3], deg=[0, 1, 0, 1],
            out=[{1: 2}, {}, {3: 4}, {}], inc=[set(), {0}, set(), {2}])
        for mode in ('direct', 'span', 'forest'):
            space = scalar_endomorphism_space(scan, [0, 1, 2, 3],
                preserve_grading=False, coefficient_mode=mode)
            self.assertEqual(space[2], [3, 12])
            empty = scalar_endomorphism_space(scan, [], preserve_grading=False,
                                              coefficient_mode=mode)
            self.assertEqual(empty, ([], {}, [], 0))
            connected = scalar_endomorphism_space(scan, [2, 3],
                preserve_grading=False, coefficient_mode=mode)
            self.assertEqual(connected[2], [3])
            for group in ([0], [1], [0, 0, 1]):
                with self.assertRaisesRegex(ValueError, 'scalar group'):
                    scalar_endomorphism_space(scan, group, preserve_grading=False,
                                               coefficient_mode=mode)

    def test_rectangular_and_multiple_types(self):
        rng = random.Random(261008102)
        for _ in range(100):
            source_sizes = [rng.randrange(1, 4) for _ in range(rng.randrange(1, 4))]
            target_sizes = [rng.randrange(1, 4) for _ in range(rng.randrange(1, 4))]
            if max(source_sizes + target_sizes) == 1:
                source_sizes[0] = 2
            self.compare(abstract_complex(source_sizes, target_sizes, rng))

    def test_forest_substitution_preserves_all_original_types(self):
        scan = SimpleNamespace(mid=[0, 0, 1, 1, 2, 2, 3, 3],
            deg=[0, 0, 0, 0, 1, 1, 1, 1], out=[{}, {}, {}, {}, {}, {}, {}, {}])
        # A connected coefficient forest linking four distinct matching types.
        for sources, targets, columns in [([0, 1], [4, 5], [1, 3]),
                ([2, 3], [4, 5], [3, 2]), ([2, 3], [6, 7], [2, 1])]:
            for index, source in enumerate(sources):
                for row, target in enumerate(targets):
                    if columns[index] >> row & 1:
                        scan.out[source][target] = 6
        self.compare(scan)
        stats = {}
        space = scalar_endomorphism_space(scan, list(range(8)), preserve_grading=False,
                                          coefficient_mode='forest', coefficient_stats=stats)
        self.assertEqual(stats['forest_edges'], 3)
        self.assertEqual(stats['original_variables'], 16)
        self.assertEqual(stats['reduced_variables'], 4)
        self.assertEqual(len(space[2]), 4)
        self.assertTrue(all(scan.mid[a] == scan.mid[b] and scan.deg[a] == scan.deg[b]
                            for a, b in space[1]))

    def test_homogeneous_field_search_and_recursive_witnesses(self):
        for degree, mixing in [(3, 'dense'), (4, 'bridge'), (6, 'dense')]:
            baseline = None
            for mode, reuse in [('direct', False), ('span', False), ('forest', False),
                                ('span', True), ('forest', True)]:
                scan, _ = two_field_scan(degree, mixing=mixing, fitting_primary=True,
                    fitting_coefficient_mode=mode, fitting_reuse_commutant=reuse,
                    record_witnesses=True)
                out, witness, metrics = find_scalar_split(scan, list(range(scan.live)),
                    max_variables=None, primary=True, coefficient_mode=mode)
                scan._compress([0] * scan.live)
                current = (out, witness, metrics['candidates'], scan.mid, scan.deg,
                           scan.out, scan.weights, scan.fitting_witnesses)
                if baseline is None:
                    baseline = current
                else:
                    self.assertEqual(current, baseline)
                scan.check_d_squared()

    def test_natural_knot_scan_equivalence(self):
        for name in ('conway', 'kinoshita_terasaka', 'stress_braid5_36'):
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
            direct = fitting_khovanov_rank(diagram.pd, fitting_primary=True,
                                           record_witnesses=True, check_d_squared=True)
            for mode in ('span', 'forest'):
                current = fitting_khovanov_rank(diagram.pd, fitting_primary=True,
                    fitting_coefficient_mode=mode, record_witnesses=True, check_d_squared=True,
                    order=direct['order'])
                self.assertEqual(current['by_degree'], direct['by_degree'])
                self.assertEqual(current['witnesses'], direct['witnesses'])
                self.assertEqual(current['stages'], direct['stages'])
                self.assertGreater(current['stats']['fitting_coefficient_blocks'], 0)

    def test_limits_validation_and_interruption(self):
        scan, _ = two_field_scan(4, mixing='dense')
        for bad in (None, False, 1, 'automatic', [], {}):
            with self.assertRaises(ValueError):
                FittingScan(fitting_coefficient_mode=bad)
            with self.assertRaises(ValueError):
                scalar_endomorphism_space(scan, list(range(scan.live)), coefficient_mode=bad)
        for mode in ('span', 'forest'):
            stats = {}
            self.assertIsNone(scalar_endomorphism_space(scan, list(range(scan.live)),
                max_variables=1, coefficient_mode=mode, coefficient_stats=stats))
            self.assertEqual(stats, {})
            for allowance in (1, 40, 180):
                saved = copy.deepcopy((scan.mid, scan.deg, scan.out))
                remaining = allowance
                def check():
                    nonlocal remaining
                    remaining -= 1
                    if remaining == 0:
                        raise InterruptedError('research test interruption')
                with self.assertRaises(InterruptedError):
                    scalar_endomorphism_space(scan, list(range(scan.live)), coefficient_mode=mode,
                                              check=check)
                self.assertEqual((scan.mid, scan.deg, scan.out), saved)


if __name__ == '__main__':
    unittest.main(verbosity=2)
