"""Independent arithmetic, complete-conjugation and resource checks."""
import copy
import json
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot import Diagram, khovanov_rank
from fastunknot.geometry import ScanLimit
from fastunknot.primary_split import (berlekamp_basis, evaluate_polynomial,
    minimal_polynomial, primary_projector, verify_primary_projector)
from fastunknot.scalar_split import (FittingScan, _fitting_bases,
    find_scalar_split, fitting_khovanov_rank, fitting_khovanov_decide)
from primary_research.families import (inverse_matrix, multiplication_matrix,
    poly_multiply, poly_remainder, two_field_scan)
from test_scalar_split import verify_witness


def dense(matrix):
    return [[(column >> row) & 1 for column in matrix] for row in range(len(matrix))]


def dense_product(left, right):
    size = len(left)
    return [[sum(left[i][k] * right[k][j] for k in range(size)) % 2
             for j in range(size)] for i in range(size)]


def dense_polynomial(matrix, polynomial):
    """Independent dense evaluation by multiplying out successive powers."""
    size = len(matrix)
    power = [[int(i == j) for j in range(size)] for i in range(size)]
    value = [[0] * size for _ in range(size)]
    while polynomial:
        if polynomial & 1:
            value = [[x ^ y for x, y in zip(a, b)] for a, b in zip(value, power)]
        power = dense_product(power, matrix)
        polynomial >>= 1
    return value


def independently_verify_projector(candidate, projector, evidence):
    for source, claimed in zip(candidate, projector):
        q, p = dense(source), dense(claimed)
        zero = [[0] * len(source) for _ in source]
        assert dense_polynomial(q, evidence['minimal_polynomial']) == zero
        assert dense_polynomial(q, evidence['projector_polynomial']) == p
        assert dense_product(p, p) == p
    assert any(any(block) for block in projector)
    assert any(block != [1 << i for i in range(len(block))] for block in projector)


class PrimaryAlgebraTests(unittest.TestCase):
    def test_fixed_space_exhaustive_including_repeated_factors(self):
        for degree in range(1, 7):
            for modulus in range(1 << degree, 1 << (degree + 1)):
                basis = berlekamp_basis(modulus)
                represented = {0}
                for vector in basis:
                    represented |= {old ^ vector for old in list(represented)}
                expected = {p for p in range(1 << degree)
                            if poly_remainder(poly_multiply(p, p) ^ p, modulus) == 0}
                self.assertEqual(represented, expected)
                self.assertEqual(len(represented), 1 << len(basis))

    def test_minimal_polynomial_small_matrices_by_exhaustion(self):
        rng = random.Random(63017)
        cases = [[packed & 3, packed >> 2] for packed in range(16)]
        cases += [[rng.randrange(8) for _ in range(3)] for _ in range(30)]
        for matrix in cases:
            size = len(matrix)
            zero = [[0] * size for _ in range(size)]
            expected = next(polynomial
                for degree in range(1, size + 1)
                for polynomial in range(1 << degree, 1 << (degree + 1))
                if dense_polynomial(dense(matrix), polynomial) == zero)
            self.assertEqual(minimal_polynomial([matrix]), expected)

    def test_invertible_candidate_and_repeated_primary_factor(self):
        f, g = 0b1011, 0b1101
        modulus = poly_multiply(poly_multiply(f, f), g)
        matrix = multiplication_matrix(2, modulus)
        self.assertEqual(minimal_polynomial([matrix]), modulus)
        self.assertEqual(_fitting_bases([list(range(9))], [matrix])[2], 9)
        projector, evidence = primary_projector([matrix])
        self.assertEqual(evidence['berlekamp_dimension'], 2)
        self.assertTrue(verify_primary_projector([matrix], projector, evidence))
        independently_verify_projector([matrix], projector, evidence)
        # Nontrivial decomposition of the ambient vector space is not enough:
        # a repeated copy with a single irreducible spectrum remains primary.
        block = multiplication_matrix(2, f)
        self.assertIsNone(primary_projector([block, block])[0])
        nilpotent = [2, 4, 0]
        self.assertIsNone(primary_projector([nilpotent])[0])

    def test_certificate_corruption(self):
        candidate = [multiplication_matrix(2, 0b1011), multiplication_matrix(2, 0b1101)]
        projector, evidence = primary_projector(candidate)
        self.assertTrue(verify_primary_projector(candidate, projector, evidence))
        broken = copy.deepcopy(projector)
        broken[0][0] ^= 1
        with self.assertRaises(ArithmeticError):
            verify_primary_projector(candidate, broken, evidence)
        broken_evidence = dict(evidence, projector_polynomial=evidence['projector_polynomial'] ^ 2)
        with self.assertRaises(ArithmeticError):
            verify_primary_projector(candidate, projector, broken_evidence)
        broken_evidence = dict(evidence, minimal_polynomial=evidence['minimal_polynomial'] ^ 2)
        with self.assertRaises(ArithmeticError):
            verify_primary_projector(candidate, projector, broken_evidence)

    def test_global_minimal_polynomial_and_zero_dimensional_blocks(self):
        blocks = [[], [0], [1]]
        self.assertEqual(minimal_polynomial(blocks), 0b110)
        projector, evidence = primary_projector(blocks)
        self.assertTrue(verify_primary_projector(blocks, projector, evidence))
        independently_verify_projector(blocks, projector, evidence)
        for bad in ([], [[]], [[-1]], [[2]], [[True]]):
            with self.assertRaises(ValueError):
                primary_projector(bad)


class PrimaryScannerTests(unittest.TestCase):
    def test_actual_default_candidate_policy_miss_and_primary_split(self):
        # Both sizes fit the unchanged 48-object / 1024-variable defaults.
        for degree in (8, 10):
            scan, fixture = two_field_scan(degree, mixing='dense')
            group = list(range(scan.live))
            old_rows, old_witness, old_metrics = find_scalar_split(scan, group)
            rows, witness, metrics = find_scalar_split(scan, group, primary=True)
            self.assertIsNone(old_rows)
            self.assertIsNone(old_witness)
            self.assertEqual(old_metrics['candidates'], 2 * degree + 16)
            self.assertIsNotNone(rows)
            self.assertEqual(metrics['primary_splits'], 1)
            self.assertEqual(metrics['candidates'], 2)
            self.assertTrue(verify_primary_projector(
                witness['primary']['candidate_columns'], witness['endomorphism_columns'],
                witness['primary']))
            # Independent full-differential verifier checks all attachments.
            from fastunknot.recovered_grading import recover_shifts
            shifts = recover_shifts(scan, group)
            witness.update(rows=scan.out, transformed_rows=rows, degrees=scan.deg,
                matchings=[scan.algebra.pairs[m] for m in scan.mid],
                quantum_shifts=[shifts[v] for v in group], preserves_quantum_grading=True)
            self.assertTrue(verify_witness(witness))
            self.assertTrue(verify_witness(json.loads(json.dumps(witness))))

    def test_whole_component_split_cache_and_negative_policy_isolation(self):
        baseline, _ = two_field_scan(8, mixing='dense', record_witnesses=True)
        baseline._compress([0] * baseline.live)
        self.assertEqual(baseline.stats['fitting_splits'], 0)
        scan, _ = two_field_scan(8, mixing='dense', fitting_primary=True, record_witnesses=True)
        scan.scalar_cache = dict(baseline.scalar_cache)
        scan._compress([0] * scan.live)
        self.assertEqual(scan.stats['fitting_primary_splits'], 1)
        self.assertEqual(scan.stats['fitting_splits'], 1)
        self.assertEqual(len(scan.weights), 2)
        scan.check_d_squared()
        again, _ = two_field_scan(8, mixing='dense', fitting_primary=True, record_witnesses=True)
        again.scalar_cache = dict(scan.scalar_cache)
        again._compress([0] * again.live)
        self.assertGreater(again.stats['fitting_cache_hits'], 0)
        self.assertEqual(again.stats['fitting_primary_candidates'], 0)
        self.assertEqual(again.out, scan.out)
        for witness in again.fitting_witnesses:
            self.assertTrue(verify_witness(witness))

    def test_different_matching_attachments_and_grading_are_retained(self):
        scan, _ = two_field_scan(6, mixing='dense', fitting_primary=True, record_witnesses=True)
        size = scan.live // 2
        old_size = scan.live
        other = scan.algebra.intern(((0, 3), (1, 2)))
        scan.mid.extend([other] * size)
        scan.deg.extend([1] * size)
        scan.out.extend({} for _ in range(size))
        scan.inc.extend(set() for _ in range(size))
        scan.owner.extend([0] * size)
        scan.live += size
        scan.fitting_max_objects = scan.live
        scan.fitting_max_variables = 3 * size * size
        for source in range(size):
            scan.out[source][old_size + source] = 1
            scan.inc[old_size + source].add(source)
        scan._compress([0] * scan.live)
        self.assertGreater(scan.stats['fitting_primary_splits'], 0)
        for witness in scan.fitting_witnesses:
            self.assertTrue(verify_witness(witness))
            self.assertEqual(len(set(tuple(map(tuple, m)) for m in witness['matchings'])), 2)
            self.assertEqual(set(witness['quantum_shifts']), {0, 1, 2})
            if 'primary' in witness:
                self.assertTrue(verify_primary_projector(witness['primary']['candidate_columns'],
                    witness['endomorphism_columns'], witness['primary']))
        scan.check_d_squared()

    def test_caps_and_interrupted_discovery_preserve_the_current_differential(self):
        scan, _ = two_field_scan(8, mixing='dense', fitting_primary=True, fitting_max_variables=8)
        original = copy.deepcopy((scan.mid, scan.deg, scan.out, scan.inc))
        scan._compress([0] * scan.live)
        self.assertEqual(scan.stats['fitting_primary_candidates'], 0)
        self.assertEqual(scan.stats['fitting_splits'], 0)
        self.assertEqual((scan.mid, scan.deg, scan.out, scan.inc), original)
        scan, fixture = two_field_scan(8, mixing='dense', fitting_primary=True)
        original = copy.deepcopy((scan.mid, scan.deg, scan.out, scan.inc))
        calls = 0
        def interrupt():
            nonlocal calls
            calls += 1
            if calls == 120:
                raise ScanLimit('test interruption')
        with self.assertRaises(ScanLimit):
            find_scalar_split(scan, list(range(scan.live)), check=interrupt, primary=True)
        self.assertEqual((scan.mid, scan.deg, scan.out, scan.inc), original)
        self.assertIsNotNone(find_scalar_split(scan, list(range(scan.live)), primary=True)[0])

    def test_real_diagrams_and_capped_contract(self):
        for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8'):
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
            reference = khovanov_rank(diagram.pd)
            actual = fitting_khovanov_rank(diagram.pd, fitting_primary=True,
                record_witnesses=True, check_d_squared=True)
            decision = fitting_khovanov_decide(diagram.pd, fitting_primary=True, check_d_squared=True)
            self.assertEqual(actual['by_degree'], reference['by_degree'])
            self.assertEqual(decision['rank_capped'], min(3, reference['rank']))
            self.assertEqual(actual['backend'], 'scalar-primary-interval-sharing')
            for witness in actual['witnesses']:
                self.assertTrue(verify_witness(witness))
                if 'primary' in witness:
                    self.assertTrue(verify_primary_projector(witness['primary']['candidate_columns'],
                        witness['endomorphism_columns'], witness['primary']))

    def test_small_braids_multiple_orders(self):
        rng = random.Random(819205)
        tested = 0
        while tested < 15:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(3, 12))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            order = list(range(len(word)))
            rng.shuffle(order)
            expected = khovanov_rank(diagram.pd, order=order)
            actual = fitting_khovanov_rank(diagram.pd, order=order, fitting_primary=True,
                                          check_d_squared=True)
            self.assertEqual(actual['by_degree'], expected['by_degree'])
            tested += 1

    def test_boolean_contract_including_empty_input(self):
        for value in (1, 0, None, 'yes'):
            with self.assertRaises(ValueError):
                FittingScan(fitting_primary=value)
            with self.assertRaises(ValueError):
                fitting_khovanov_rank([], fitting_primary=value)
        self.assertEqual(fitting_khovanov_rank([], fitting_primary=True)['backend'],
                         'scalar-primary-interval-sharing')


if __name__ == '__main__':
    unittest.main(verbosity=2)
