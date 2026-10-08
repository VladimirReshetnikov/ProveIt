"""Exact commutant-corner inheritance, including deterministic search equivalence."""
import json
import copy
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot import Diagram
from fastunknot.component_scan import components
from fastunknot.scalar_split import (
    FittingScan, _View, _canonical_binary_span, _change_basis, _columns,
    _commutes, _fitting_bases, _inherited_endomorphism_spaces, _inverse,
    _monogenic_child_spaces, binary_nullspace,
    find_scalar_split, fitting_khovanov_decide, fitting_khovanov_rank,
    scalar_endomorphism_space, verify_scalar_local_certificate,
)
from test_scalar_split import mixed_copies, verify_witness


def random_change(size, rng):
    columns = [1 << index for index in range(size)]
    for _ in range(5 * size):
        source, target = rng.sample(range(size), 2)
        columns[target] ^= columns[source]
    return columns


def two_term_direct_sum(rng):
    """Random honest homogeneous two-term complexes over a two-dot algebra."""
    scan = FittingScan(shape_cache=False)
    matching = scan.algebra.intern(((0, 1), (2, 3)))
    scan.points = frozenset(range(4))
    scan.mid, scan.deg, scan.out = [], [], []
    for _ in range(rng.randrange(2, 5)):
        sources = list(range(len(scan.mid), len(scan.mid) + rng.randrange(1, 4)))
        targets = list(range(sources[-1] + 1, sources[-1] + 1 + rng.randrange(1, 4)))
        scan.mid.extend([matching] * (len(sources) + len(targets)))
        scan.deg.extend([0] * len(sources) + [1] * len(targets))
        # Coefficients are x, y, or x+y, all of quantum dot degree one.
        scan.out.extend([{target: rng.choice((2, 4, 6)) for target in targets}
                         for _ in sources] + [{} for _ in targets])
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    return scan


class CanonicalSpanTests(unittest.TestCase):
    def test_agrees_with_nullspace_basis_after_generator_changes(self):
        rng = random.Random(2026100801)
        for variables in range(1, 65):
            for _ in range(8):
                equations = [rng.getrandbits(variables)
                             for _ in range(rng.randrange(variables + 5))]
                basis = binary_nullspace(equations, variables)
                generators = list(basis)
                for _ in range(12):
                    vector = 0
                    for item in basis:
                        if rng.randrange(2):
                            vector ^= item
                    generators.append(vector)
                rng.shuffle(generators)
                self.assertEqual(_canonical_binary_span(generators), basis)

    def test_corner_compression_is_not_multiplicative(self):
        # e=E11, a=E12, b=E21 in M_2(F2): eabe=e but eae=ebe=0.
        from fastunknot.barcode_scan import _apply
        a, b = [0, 1], [2, 0]
        product = [_apply(a, column) for column in b]
        self.assertEqual(product[0] & 1, 1)
        self.assertEqual((a[0] & 1) * (b[0] & 1), 0)


class CornerTests(unittest.TestCase):
    def test_random_two_term_corners_equal_fresh_complete_spaces(self):
        rng = random.Random(2026100802)
        accepted = 0
        for _ in range(300):
            if accepted == 60:
                break
            scan = two_term_direct_sum(rng)
            group = list(range(scan.live))
            blocks = [[v for v in group if scan.deg[v] == degree] for degree in (0, 1)]
            changes = [random_change(len(block), rng) for block in blocks]
            mixed_rows, _ = _change_basis(scan, group, blocks, changes, [0, 0])
            mixed = _View(scan, group, out=mixed_rows)
            if len(list(components(mixed))) != 1:
                # Relative shifts are independently normalized on disconnected
                # graph components; the production API takes one whole component.
                continue
            accepted += 1
            data = scalar_endomorphism_space(mixed, group, max_variables=None)
            self.assertEqual(data[0], blocks)
            inverse_changes = [_inverse(change) for change in changes]
            restored_rows, _ = _change_basis(mixed, group, blocks, inverse_changes, [0, 0])
            restored = _View(mixed, group, out=restored_rows)
            self.assertEqual(restored.out, scan.out)
            children = list(components(restored))
            inherited = _inherited_endomorphism_spaces(data, group, inverse_changes, children)
            for method in ('direct', 'matrix_units'):
                self.assertEqual(inherited, _inherited_endomorphism_spaces(
                    data, group, inverse_changes, children, method=method))
            for child, corner in zip(children, inherited):
                fresh = scalar_endomorphism_space(restored, child, max_variables=None)
                self.assertEqual(corner[:3], fresh[:3])
                self.assertEqual(corner[3], 0)
                child_blocks, variables, basis, _ = corner
                self.assertTrue(all(_commutes(restored, child, child_blocks,
                                               _columns(child_blocks, variables, vector))
                                    for vector in basis))
                old = find_scalar_split(restored, child, endomorphism_data=fresh)
                new = find_scalar_split(restored, child, endomorphism_data=corner)
                self.assertEqual(old[:2], new[:2])
        self.assertEqual(accepted, 60)

    def test_selected_children_and_nonconsecutive_parent_indices(self):
        original = mixed_copies(FittingScan, 6)
        # Pad a dead object before the connected component; the inherited map
        # must use group-local indices rather than original scan indices.
        original.mid.insert(0, None)
        original.deg.insert(0, 0)
        original.out = [{}] + [{target + 1: value for target, value in row.items()}
                              for row in original.out]
        original.inc = [set() for _ in original.mid]
        for source, row in enumerate(original.out):
            for target in row:
                original.inc[target].add(source)
        group = list(range(1, len(original.mid)))
        data = scalar_endomorphism_space(original, group)
        out, witness, _ = find_scalar_split(original, group, endomorphism_data=data)
        changed = _View(original, group, out=out)
        children = list(components(changed))
        selected = [max(children, key=len)]
        corners = _inherited_endomorphism_spaces(data, group, witness['basis_columns'], selected)
        self.assertEqual(corners[0][:3], scalar_endomorphism_space(changed, selected[0])[:3])

    def test_callback_interrupts_transport(self):
        scan = mixed_copies(FittingScan, 4)
        group = list(range(scan.live))
        data = scalar_endomorphism_space(scan, group)
        out, witness, _ = find_scalar_split(scan, group, endomorphism_data=data)
        changed = _View(scan, group, out=out)

        def stop():
            raise TimeoutError('test cancellation')

        with self.assertRaises(TimeoutError):
            _inherited_endomorphism_spaces(data, group, witness['basis_columns'],
                                           list(components(changed)), stop)


class RecursiveTests(unittest.TestCase):
    def test_recursive_witnesses_and_equation_count_reduction(self):
        for copies in (2, 3, 6, 12, 16):
            answers = []
            for reuse in (False, True):
                scan = mixed_copies(FittingScan, copies, fitting_reuse_endomorphisms=reuse,
                                    record_witnesses=True, fitting_max_splits=32,
                                    fitting_cache_entries=0)
                scan._compress([0] * scan.live)
                answers.append(scan)
                for witness in scan.fitting_witnesses:
                    self.assertTrue(verify_witness(json.loads(json.dumps(witness))))
            old, new = answers
            self.assertEqual((new.mid, new.deg, new.out, new.weights),
                             (old.mid, old.deg, old.out, old.weights))
            self.assertEqual(new.fitting_witnesses, old.fitting_witnesses)
            self.assertEqual(old.stats['fitting_endomorphism_computations'], copies - 1)
            self.assertEqual(new.stats['fitting_endomorphism_computations'], 1)
            self.assertEqual(old.stats['fitting_equations_built'],
                             2 * sum(size * size for size in range(2, copies + 1)))
            self.assertEqual(new.stats['fitting_equations_built'], 2 * copies * copies)

    def test_cache_hits_and_split_budget_keep_identical_results(self):
        for budget in (0, 1, 3, 8):
            old = mixed_copies(FittingScan, 7, fitting_reuse_endomorphisms=False,
                               fitting_max_splits=budget, record_witnesses=True)
            old._compress([0] * old.live)
            new = mixed_copies(FittingScan, 7, fitting_reuse_endomorphisms=True,
                               fitting_max_splits=budget, record_witnesses=True)
            new.scalar_cache = dict(old.scalar_cache)
            new._compress([0] * new.live)
            self.assertEqual((new.mid, new.deg, new.out, new.weights),
                             (old.mid, old.deg, old.out, old.weights))
            self.assertEqual(new.fitting_witnesses, old.fitting_witnesses)

    def test_named_natural_rank_and_decision_agreement(self):
        for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8', 'torus_3_5'):
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
            old = fitting_khovanov_rank(diagram.pd, fitting_reuse_endomorphisms=False,
                                       record_witnesses=True, check_d_squared=True)
            new = fitting_khovanov_rank(diagram.pd, fitting_reuse_endomorphisms=True,
                                       record_witnesses=True, check_d_squared=True)
            self.assertEqual(old['by_degree'], new['by_degree'])
            self.assertEqual(old['witnesses'], new['witnesses'])
            decision = fitting_khovanov_decide(diagram.pd, fitting_reuse_endomorphisms=True,
                                               check_d_squared=True)
            self.assertEqual(decision['rank_capped'], min(3, old['rank']))

    def test_reuse_option_requires_boolean(self):
        with self.assertRaises(ValueError):
            FittingScan(fitting_reuse_endomorphisms=1)


def matrix_complex(matrix):
    """A two-term coefficient representation with full commutant Z(matrix)."""
    scan = FittingScan(shape_cache=False)
    size = len(matrix)
    matching = scan.algebra.intern(((0, 1), (2, 3)))
    scan.points = frozenset(range(4))
    scan.mid, scan.deg = [matching] * (2 * size), [0] * size + [1] * size
    scan.out = [{} for _ in scan.mid]
    for source in range(size):
        for target in range(size):
            value = (2 if source == target else 0) ^ (4 if matrix[source] >> target & 1 else 0)
            if value:
                scan.out[source][size + target] = value
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    return scan


def certificate_scan(evidence):
    scan = FittingScan(shape_cache=False)
    scan.points = frozenset(evidence['frontier_points'])
    scan.mid = [scan.algebra.intern(tuple(map(tuple, matching))) for matching in evidence['matchings']]
    scan.deg = list(evidence['degrees'])
    scan.out = [{int(target): value for target, value in row.items()} for row in evidence['rows']]
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    return scan


class LocalCertificateTests(unittest.TestCase):
    def test_local_field_and_repeated_primary_factor_exhaustively(self):
        from fastunknot.barcode_scan import _apply
        from primary_research.families import multiplication_matrix
        for modulus in (0b1011, 0b10101):
            # F8, and F2[t]/((t^2+t+1)^2), respectively.
            scan = matrix_complex(multiplication_matrix(2, modulus))
            group = list(range(scan.live))
            old = find_scalar_split(scan, group, primary=True, certify_local=False)
            new = find_scalar_split(scan, group, primary=True, certify_local=True)
            self.assertEqual(old[:2], (None, None))
            self.assertEqual(new[:2], (None, None))
            certificate = new[2]['local_certificate']
            self.assertIsNotNone(certificate)
            self.assertTrue(verify_scalar_local_certificate(scan, group, certificate))
            self.assertLess(new[2]['candidates'], old[2]['candidates'])
            blocks, variables, basis, _ = scalar_endomorphism_space(scan, group)
            idempotents = []
            for mask in range(1 << len(basis)):
                vector = 0
                for index, item in enumerate(basis):
                    if mask >> index & 1:
                        vector ^= item
                columns = _columns(blocks, variables, vector)
                square = [[_apply(matrix, column) for column in matrix] for matrix in columns]
                if square == columns:
                    idempotents.append(vector)
            self.assertEqual(len(idempotents), 2)
            for key in ('commutant_dimension', 'minimal_polynomial', 'minimal_degree',
                        'berlekamp_dimension'):
                bad = copy.deepcopy(certificate)
                bad[key] += 1
                with self.assertRaises(ArithmeticError):
                    verify_scalar_local_certificate(scan, group, bad)

    def test_primary_generator_without_saturation_does_not_certify(self):
        from fastunknot.primary_split import primary_projector
        from primary_research.families import two_field_scan
        scan, _ = two_field_scan(3, mixing='dense')
        group = list(range(scan.live))
        blocks, _, basis, _ = scalar_endomorphism_space(scan, group)
        identity = [[1 << col for col in range(len(block))] for block in blocks]
        projector, evidence = primary_projector(identity)
        self.assertIsNone(projector)
        self.assertEqual(evidence['berlekamp_dimension'], 1)
        self.assertLess(evidence['minimal_degree'], len(basis))
        certificate = dict(blocks=blocks, generator_columns=identity,
                           commutant_dimension=len(basis), **evidence)
        with self.assertRaises(ArithmeticError):
            verify_scalar_local_certificate(scan, group, certificate)
        self.assertIsNotNone(find_scalar_split(scan, group, primary=True, certify_local=True)[1])

    def test_monogenic_transport_reconstructs_nonlocal_corner(self):
        from fastunknot.primary_split import primary_projector
        from primary_research.families import multiplication_matrix
        # Three distinct degree-four irreducibles. The first binary cut leaves
        # one local corner and one corner with two primary factors.
        direct = []
        for index, modulus in enumerate((0b10011, 0b11001, 0b11111)):
            direct.extend(column << (4 * index) for column in multiplication_matrix(2, modulus))
        scan = matrix_complex(direct)
        group = list(range(scan.live))
        data = scalar_endomorphism_space(scan, group)
        blocks, _, basis, _ = data
        projector, evidence = primary_projector([direct, direct])
        self.assertEqual(evidence['minimal_degree'], len(basis))
        self.assertEqual(len(basis), 12)
        changes, kernels, _, _ = _fitting_bases(blocks, projector)
        rows, _ = _change_basis(scan, group, blocks, changes, kernels)
        changed = _View(scan, group, out=rows)
        # Use the two projector sides, which are differential-closed sums; the
        # general corner theorem applies to these selected direct summands too.
        sides = [[], []]
        for block, kernel in zip(blocks, kernels):
            sides[0].extend(block[:kernel])
            sides[1].extend(block[kernel:])
        children = [sorted(side) for side in sides]
        witness = dict(blocks=blocks, basis_columns=changes,
                       primary=dict(evidence, candidate_columns=[direct, direct]))
        corners = _monogenic_child_spaces(witness, children)
        self.assertEqual(sum(certificate is not None for _, certificate in corners), 1)
        for child, (corner, certificate) in zip(children, corners):
            if certificate is not None:
                self.assertTrue(verify_scalar_local_certificate(changed, child, certificate))
            else:
                fresh = scalar_endomorphism_space(changed, child)
                self.assertEqual(corner[:3], fresh[:3])
                self.assertEqual(len(corner[2]), 8)

    def test_field_pair_paths_preserve_splits_and_verify_recorded_local_leaves(self):
        from primary_research.families import two_field_scan
        for degree in (3, 6, 8, 10, 12):
            baseline, _ = two_field_scan(degree, mixing='dense', fitting_primary=True,
                                         fitting_reuse_endomorphisms=False, record_witnesses=True)
            baseline._compress([0] * baseline.live)
            for options in (dict(fitting_reuse_endomorphisms=True),
                            dict(fitting_reuse_endomorphisms=False, fitting_certify_local=True),
                            dict(fitting_reuse_endomorphisms=True, fitting_certify_local=True,
                                 fitting_monogenic_corners=True)):
                scan, _ = two_field_scan(degree, mixing='dense', fitting_primary=True,
                                         record_witnesses=True, **options)
                scan._compress([0] * scan.live)
                self.assertEqual((scan.mid, scan.deg, scan.out, scan.weights),
                                 (baseline.mid, baseline.deg, baseline.out, baseline.weights))
                self.assertEqual(scan.fitting_witnesses, baseline.fitting_witnesses)
                for certificate in scan.fitting_local_certificates:
                    saved = json.loads(json.dumps(certificate))
                    view = certificate_scan(saved)
                    self.assertTrue(verify_scalar_local_certificate(view, list(range(view.live)), saved))
                if options.get('fitting_monogenic_corners') and degree in (8, 10, 12):
                    self.assertEqual(scan.stats['fitting_candidates'], 2)
                    self.assertEqual(scan.stats['fitting_endomorphism_computations'], 1)
                    self.assertEqual(scan.stats['fitting_monogenic_corners'], 2)


if __name__ == '__main__':
    unittest.main(verbosity=2)
