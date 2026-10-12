"""Independent finite covering oracles for the compact-surface spectrum."""

from collections import Counter
from copy import deepcopy
from itertools import product
import unittest
from unittest.mock import patch

from fastunknot.topology_spectrum import (
    recover_topology_spectrum,
    scale_core_spectrum,
    verify_scaled_spectrum,
    verify_topology_spectrum,
)


def _oracle(types):
    """Build histograms by disjoint union of named classification types.

    A tuple is (orientable, genus_or_crosscaps, boundary_circles, count).
    The connected orientation cover of a k-crosscap surface has genus k-1.
    This oracle never uses the recovery recurrence.
    """
    base, double, expected = Counter(), Counter(), Counter()
    for orientable, handles, boundary, count in types:
        if not count:
            continue
        chi = 2 - (2 * handles if orientable else handles) - boundary
        base[chi, boundary] += count
        if orientable:
            double[chi, boundary] += 2 * count
        else:
            cover_genus, cover_boundary = handles - 1, 2 * boundary
            double[2 - 2 * cover_genus - cover_boundary, cover_boundary] += count
        expected[chi, boundary, orientable, handles] += count
    rows = []
    for (chi, boundary, orientable, handles), count in sorted(
            expected.items(), key=lambda item: (item[0][0], item[0][1], not item[0][2])):
        row = dict(chi=chi, boundary_components=boundary,
                   orientable=orientable, multiplicity=count)
        row['genus' if orientable else 'crosscaps'] = handles
        rows.append(row)
    return dict(base), dict(double), rows


class TopologySpectrumTests(unittest.TestCase):
    def test_exhaustive_small_valid_multisets(self):
        # 3^8 = 6,561 spectra include sphere/projective-plane and
        # annulus/Mobius cover collisions, and the torus/Klein zero class.
        types = [
            (True, 0, 0), (False, 1, 0), (True, 0, 1), (False, 1, 1),
            (True, 0, 2), (True, 1, 0), (False, 2, 0), (True, 2, 0),
        ]
        for multiplicities in product(range(3), repeat=len(types)):
            source = [(*kind, count) for kind, count in zip(types, multiplicities)]
            base, double, expected = _oracle(source)
            actual = recover_topology_spectrum(base, double)
            self.assertEqual(actual, expected, multiplicities)
            self.assertTrue(verify_topology_spectrum(base, double, actual))

    def test_doubling_chain_collisions(self):
        # At each of (-2,0), (-4,0), (-8,0) both orientation types occur.
        # A cover contribution from the preceding signature collides with
        # two copies of orientable components at the following signature.
        types = [(True, g, 0) for g in (2, 3, 5)]
        types += [(False, k, 0) for k in (4, 6, 10)]
        for multiplicities in product(range(3), repeat=len(types)):
            source = [(*kind, count) for kind, count in zip(types, multiplicities)]
            base, double, expected = _oracle(source)
            self.assertEqual(recover_topology_spectrum(base, double), expected)
            self.assertTrue(verify_topology_spectrum(base, double, expected))

    def test_zero_vector_and_empty_histograms(self):
        for tori in range(7):
            for klein in range(7):
                base, double, expected = _oracle([
                    (True, 1, 0, tori), (False, 2, 0, klein)])
                self.assertEqual(recover_topology_spectrum(base, double), expected)
        self.assertEqual(recover_topology_spectrum({}, {}), [])
        self.assertTrue(verify_topology_spectrum({}, {}, []))
        self.assertFalse(verify_topology_spectrum({}, {(0, 0): 1}, []))

    def test_cover_only_support_is_required(self):
        base, double, expected = _oracle([(False, 3, 2, 7)])
        self.assertEqual(set(base), {(-3, 2)})
        self.assertEqual(set(double), {(-6, 4)})
        self.assertEqual(recover_topology_spectrum(base, double), expected)
        for bad in ({}, {(-6, 4): 8}, {(-6, 4): 7, (0, 0): 1}):
            with self.assertRaises(ValueError):
                recover_topology_spectrum(base, bad)
            self.assertFalse(verify_topology_spectrum(base, bad, expected))

    def test_sparse_huge_values_and_multiplicities(self):
        huge = (1 << 20001) + 17
        source = [(True, huge, 3, huge + 1), (False, huge + 1, 4, huge)]
        base, double, expected = _oracle(source)
        self.assertEqual(recover_topology_spectrum(base, double), expected)
        self.assertTrue(verify_topology_spectrum(base, double, expected))
        # The chain has a missing predecessor; no scan up to its magnitude
        # or across all possible component signatures is permissible.
        self.assertEqual(len(expected), 2)

    def test_weight_engine_rows_and_hexadecimal_codec(self):
        base, double, expected = _oracle([(False, 3, 2, 11), (True, 2, 2, 5)])

        def encode(histogram):
            return [dict(weight=[hex(x) for x in key], orbits=hex(count))
                    for key, count in sorted(histogram.items())]

        self.assertEqual(recover_topology_spectrum(encode(base), encode(double)), expected)
        encoded_rows = [{key: hex(value) if type(value) is int else value
                         for key, value in row.items()} for row in expected]
        self.assertTrue(verify_topology_spectrum(encode(base), encode(double), encoded_rows))

    def test_impossible_histograms_are_rejected(self):
        cases = [
            ({(1, 1): 1}, {(1, 1): 1}),
            ({(1, 1): 1}, {}),
            ({(2, 0): 1}, {}),
            ({(0, 0): 2}, {(0, 0): 1}),
            ({(0, 0): 2}, {(0, 0): 5}),
            ({(3, 0): 1}, {(3, 0): 2}),
            ({(0, -1): 1}, {}),
            ({(0, 0): -1}, {}),
            ({(0, 0): True}, {}),
            ({(True, 0): 1}, {}),
            ({(0, False): 1}, {}),
            ({(0, 0): 1.0}, {}),
            ({(0, 0): '1'}, {}),
        ]
        for base, double in cases:
            with self.subTest(base=base, double=double):
                with self.assertRaises(ValueError):
                    recover_topology_spectrum(base, double)
                self.assertFalse(verify_topology_spectrum(base, double, []))
        duplicate = [dict(weight=[0, 0], orbits=1), dict(weight=[0, 0], orbits=1)]
        with self.assertRaises(ValueError):
            recover_topology_spectrum(duplicate, {(0, 0): 4})

    def test_independent_verifier_and_mutations(self):
        base, double, expected = _oracle([
            (True, 0, 1, 3), (False, 3, 2, 5), (True, 1, 0, 7), (False, 2, 0, 11)])
        with patch('fastunknot.topology_spectrum.recover_topology_spectrum',
                   side_effect=AssertionError('producer must not run')):
            self.assertTrue(verify_topology_spectrum(base, double, expected))
            mutations = [list(reversed(expected)), expected[:-1], expected + [expected[-1]]]
            for field, replacement in [('chi', 7), ('boundary_components', 9),
                                       ('orientable', 1), ('multiplicity', 6),
                                       ('crosscaps', 100)]:
                bad = deepcopy(expected)
                bad[0][field] = replacement
                mutations.append(bad)
            bad = deepcopy(expected)
            bad[0]['unexpected'] = 0
            mutations.append(bad)
            for bad in mutations:
                self.assertFalse(verify_topology_spectrum(base, double, bad))

    def test_scaling_against_explicit_sheet_oracle(self):
        original_types = [(True, 0, 0, 2), (False, 1, 0, 3),
                          (True, 0, 2, 5), (False, 1, 1, 7),
                          (True, 1, 0, 11), (False, 2, 0, 13),
                          (True, 3, 2, 17), (False, 4, 1, 19)]
        _, _, core = _oracle(original_types)
        for divisor in range(10):
            lifted = [(True, 0, 1, 23), (True, 0, 0, 29)]
            # Explicitly form the layers only for this bounded oracle.
            for orientable, handles, boundary, count in original_types:
                if orientable:
                    for _ in range(divisor):
                        lifted.append((True, handles, boundary, count))
                else:
                    for _ in range(divisor // 2):
                        lifted.append((True, handles - 1, 2 * boundary, count))
                    if divisor % 2:
                        lifted.append((False, handles, boundary, count))
            _, _, expected = _oracle(lifted)
            actual = scale_core_spectrum(core, divisor,
                                        vertex_link_disks=23, vertex_link_spheres=29)
            self.assertEqual(actual, expected)
            self.assertTrue(verify_scaled_spectrum(core, divisor, actual,
                                                  vertex_link_disks=23,
                                                  vertex_link_spheres=29))

    def test_scaling_huge_binary_divisor(self):
        _, _, core = _oracle([(True, 0, 1, 2), (False, 2, 0, 3), (False, 1, 1, 5)])
        divisor = (1 << 20001) + 1
        result = scale_core_spectrum(core, divisor, vertex_link_disks=divisor + 7)
        self.assertTrue(verify_scaled_spectrum(core, divisor, result,
                                              vertex_link_disks=divisor + 7))
        self.assertEqual(sum(row['multiplicity'] for row in result),
                         2 * divisor + 8 * (divisor // 2) + 8 + divisor + 7)
        with patch('fastunknot.topology_spectrum.scale_core_spectrum',
                   side_effect=AssertionError('scaling producer must not run')):
            self.assertTrue(verify_scaled_spectrum(core, divisor, result,
                                                  vertex_link_disks=divisor + 7))
        bad = deepcopy(result)
        bad[0]['multiplicity'] += 1
        self.assertFalse(verify_scaled_spectrum(core, divisor, bad,
                                               vertex_link_disks=divisor + 7))

    def test_invalid_scaling_inputs(self):
        _, _, core = _oracle([(True, 0, 1, 1)])
        for divisor in (-1, True, 1.5, '2'):
            with self.assertRaises(ValueError):
                scale_core_spectrum(core, divisor)
            self.assertFalse(verify_scaled_spectrum(core, divisor, []))
        for name in ('vertex_link_disks', 'vertex_link_spheres'):
            with self.assertRaises(ValueError):
                scale_core_spectrum(core, 2, **{name: -1})
            self.assertFalse(verify_scaled_spectrum(core, 2, [], **{name: True}))

    def test_false_valued_callbacks_and_exception_propagation(self):
        class Callback:
            def __init__(self):
                self.calls = 0

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1

        base, double, expected = _oracle([(False, 3, 2, 7)])
        callback = Callback()
        recover_topology_spectrum(base, double, check=callback)
        verify_topology_spectrum(base, double, expected, check=callback)
        scaled = scale_core_spectrum(expected, 3, check=callback)
        verify_scaled_spectrum(expected, 3, scaled, check=callback)
        self.assertGreater(callback.calls, 20)

        def stop():
            raise ValueError('callback cancellation')

        for function, arguments in [
                (recover_topology_spectrum, (base, double)),
                (verify_topology_spectrum, (base, double, expected)),
                (scale_core_spectrum, (expected, 3)),
                (verify_scaled_spectrum, (expected, 3, scaled))]:
            with self.assertRaisesRegex(ValueError, 'callback cancellation'):
                function(*arguments, check=stop)


if __name__ == '__main__':
    unittest.main()
