"""Independent polynomial evaluations for the read-only first-jet query."""
import copy
from pathlib import Path
import random
import sys
from types import SimpleNamespace
import unittest

from fastunknot.first_jet import FirstJetBudget, first_jet_profile
from fastunknot.first_jet_scan import _install, first_jet_khovanov_decide
from fastunknot.geometry import ScanLimit
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reports/28/src'))
from closure_reset.cube import Cube


def polynomial_product(a, b):
    """Literal square-free monomial multiplication, independent of scanner."""
    output = 0
    for left in range(a.bit_length()):
        if not (a >> left) & 1:
            continue
        for right in range(b.bit_length()):
            if (b >> right) & 1 and not left & right:
                output ^= 1 << (left | right)
    return output


def make_scan(variables, degrees, entries):
    outgoing = [dict() for _ in degrees]
    incoming = [set() for _ in degrees]
    for source, target, coefficient in entries:
        if coefficient:
            outgoing[source][target] = coefficient
            incoming[target].add(source)
    matching = tuple((2 * i, 2 * i + 1) for i in range(variables))
    return SimpleNamespace(mid=[0] * len(degrees), deg=list(degrees),
                           out=outgoing, inc=incoming,
                           algebra=SimpleNamespace(pairs=[matching]))


def square_is_zero(scan):
    for source, row in enumerate(scan.out):
        square = {}
        for middle, first in row.items():
            for target, second in scan.out[middle].items():
                square[target] = square.get(target, 0) ^ polynomial_product(first, second)
        if any(square.values()):
            return False
    return True


def change_basis(scan, a, b, coefficient):
    """Conjugate by I + coefficient E_ab within one homological degree."""
    assert a != b and scan.deg[a] == scan.deg[b]

    def add(source, target, value):
        new = scan.out[source].get(target, 0) ^ value
        if new:
            scan.out[source][target] = new
        else:
            scan.out[source].pop(target, None)

    for target, value in list(scan.out[a].items()):
        add(b, target, polynomial_product(coefficient, value))
    for source in range(len(scan.mid)):
        add(source, a, polynomial_product(coefficient, scan.out[source].get(b, 0)))
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)


def dense_rank(matrix):
    """Dense row reduction over F2; no production packed-column rank code."""
    rows = [row[:] for row in matrix]
    if not rows:
        return 0
    pivot = 0
    for column in range(len(rows[0])):
        selected = next((i for i in range(pivot, len(rows)) if rows[i][column]), None)
        if selected is None:
            continue
        rows[pivot], rows[selected] = rows[selected], rows[pivot]
        for i in range(pivot + 1, len(rows)):
            if rows[i][column]:
                rows[i] = [a ^ b for a, b in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def evaluate_unlink(scan, arc_components):
    """Complete on circles with the specified marked-arc component labels.

    This independently substitutes into the full polynomial, including its
    higher terms, and expands the complete square-free circle module.
    """
    circles = 1 + max(arc_components)
    width = 1 << circles
    size = width * len(scan.mid)
    matrix = [[0] * size for _ in range(size)]
    for source, row in enumerate(scan.out):
        for target, coefficient in row.items():
            substituted = 0
            for monomial in range(coefficient.bit_length()):
                if not coefficient >> monomial & 1:
                    continue
                image = 0
                valid = True
                for arc, component in enumerate(arc_components):
                    if monomial >> arc & 1:
                        if image >> component & 1:
                            valid = False
                            break
                        image |= 1 << component
                if valid:
                    substituted ^= 1 << image
            for basis in range(width):
                product = polynomial_product(substituted, 1 << basis)
                for output in range(width):
                    if product >> output & 1:
                        matrix[target * width + output][source * width + basis] ^= 1
    return size - 2 * dense_rank(matrix)


class FirstJetTests(unittest.TestCase):
    def test_scalar_units_and_nonlinear_primitive_interval(self):
        # x, x+xy are different coefficients of one primitive interval.
        scan = make_scan(2, [0, 1, 2, 0, 1],
                         [(0, 1, 2), (1, 2, 10), (3, 4, 9)])
        self.assertTrue(square_is_zero(scan))
        before = copy.deepcopy(scan.__dict__)
        data = first_jet_profile(scan, range(5), audit=True)
        self.assertEqual((data['t'], data['kappa']), (3, 1))
        self.assertEqual(data['kind'], 'matching-rank')
        self.assertTrue(data['all_classical_rank_equivalent'])
        self.assertEqual(scan.__dict__, before)
        self.assertEqual(evaluate_unlink(scan, [0, 0]), 2)
        self.assertEqual(evaluate_unlink(scan, [0, 1]), 4)

    def test_contractible_and_singleton(self):
        for coefficient in (1, 3, 5, 9, 15):
            scan = make_scan(2, [3, 4], [(0, 1, coefficient)])
            data = first_jet_profile(scan, [0, 1], audit=True)
            self.assertEqual((data['t'], data['kappa']), (0, 0))
            self.assertEqual(data['kind'], 'contractible')
            self.assertEqual(evaluate_unlink(scan, [0, 1]), 0)
        scan = make_scan(3, [7], [])
        data = first_jet_profile(scan, [0], audit=True)
        self.assertEqual((data['t'], data['kappa']), (1, 1))

    def test_random_polynomial_basis_changes_preserve_queries(self):
        rng = random.Random(29001)
        for case in range(32):
            variables = 2 + case % 2
            length = 1 + case % 4
            degrees = list(range(length))
            theta = 2 | (8 if case & 1 else 0)
            entries = [(i, i + 1, theta) for i in range(length - 1)]
            for degree in range(max(1, length - 1)):
                a = len(degrees)
                degrees += [degree, degree + 1]
                entries.append((a, a + 1, 1 | rng.randrange(1 << (1 << variables))))
            scan = make_scan(variables, degrees, entries)
            original = first_jet_profile(scan, range(len(degrees)), audit=True)
            self.assertEqual((original['t'], original['kappa']), (length, 1))
            for _ in range(12):
                candidates = [(a, b) for a in range(len(degrees))
                              for b in range(len(degrees))
                              if a != b and degrees[a] == degrees[b]]
                a, b = rng.choice(candidates)
                change_basis(scan, a, b, rng.randrange(1 << (1 << variables)))
            self.assertTrue(square_is_zero(scan))
            observed = first_jet_profile(scan, range(len(degrees)), audit=True)
            self.assertEqual((observed['t'], observed['kappa']), (length, 1))
            for components in ([0] * variables, list(range(variables))):
                self.assertEqual(evaluate_unlink(scan, components),
                                 1 << (1 + max(components)))

    def test_higher_terms_do_not_enter_first_jet(self):
        # xy and xyz contribute no singleton parity, despite odd bit count.
        for coefficient in (8, 128, 136):
            scan = make_scan(3, [0, 1], [(0, 1, coefficient)])
            data = first_jet_profile(scan, [0, 1], audit=True)
            self.assertEqual((data['t'], data['kappa']), (2, 2))
            self.assertEqual(evaluate_unlink(scan, [0, 0, 0]), 4)

    def test_no_link_multiplier_claim_for_kappa_at_least_two(self):
        scan = make_scan(2, [0, 0, 1], [(0, 2, 2), (1, 2, 4)])
        data = first_jet_profile(scan, range(3), audit=True)
        self.assertEqual((data['t'], data['kappa']), (3, 2))
        self.assertFalse(data['all_classical_rank_equivalent'])
        self.assertEqual(evaluate_unlink(scan, [0, 0]), 4)
        self.assertEqual(evaluate_unlink(scan, [0, 1]), 6)
        self.assertNotEqual(evaluate_unlink(scan, [0, 1]), data['kappa'] * 4)
        even_interval = make_scan(2, [0, 1, 2], [(0, 1, 6), (1, 2, 6)])
        data = first_jet_profile(even_interval, range(3), audit=True)
        self.assertEqual(data['kappa'], 3)
        self.assertEqual(evaluate_unlink(even_interval, [0, 1]), 4)

    def test_mixed_matchings_declined_and_block_validation(self):
        scan = make_scan(2, [0, 1], [(0, 1, 2)])
        scan.mid[1] = 1
        self.assertIsNone(first_jet_profile(scan, [0, 1]))
        scan.mid[1] = 0
        for group in ([], [0, 0], [0], [1], [-1], [2]):
            with self.assertRaises(ValueError):
                first_jet_profile(scan, group)
        for value in (0, -1, True, 1 << 4):
            scan.out[0][1] = value
            with self.assertRaises(ValueError):
                first_jet_profile(scan, [0, 1])
        scan.out[0][1] = 2
        scan.deg[1] = 3
        with self.assertRaises(ValueError):
            first_jet_profile(scan, [0, 1])
        self.assertIsNone(first_jet_profile(make_scan(0, [0], []), [0]))

    def test_first_jet_audit_and_its_exact_scope(self):
        for coefficients in ((1, 1), (1, 2)):
            scan = make_scan(2, [0, 1, 2],
                             [(0, 1, coefficients[0]), (1, 2, coefficients[1])])
            with self.assertRaises(ValueError):
                first_jet_profile(scan, range(3), audit=True)
        # Necessary jet identities do not validate higher polynomial terms.
        invalid = make_scan(2, [0, 1, 2], [(0, 1, 2), (1, 2, 4)])
        self.assertFalse(square_is_zero(invalid))
        self.assertEqual(first_jet_profile(invalid, range(3), audit=True)['kappa'], 1)

    def test_local_limits_are_read_only_and_global_deadline_has_priority(self):
        scan = make_scan(2, [0, 1, 2], [(0, 1, 2), (1, 2, 10)])
        expected = first_jet_profile(scan, range(3), audit=True)
        before = copy.deepcopy(scan.__dict__)
        for allowance in (0, 1, 10, expected['work_units'] - 1):
            with self.assertRaises(FirstJetBudget):
                first_jet_profile(scan, range(3), max_work=allowance, audit=True)
            self.assertEqual(scan.__dict__, before)
        self.assertEqual(first_jet_profile(scan, range(3), audit=True)['kappa'], 1)
        for allowance in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                first_jet_profile(scan, range(3), max_work=allowance)

        def expired():
            raise ScanLimit('test global deadline')

        scan._check = expired
        with self.assertRaises(ScanLimit):
            first_jet_profile(scan, range(3), max_work=0)


class FirstJetDriverTests(unittest.TestCase):
    def test_interrupted_replacement_installation_is_transactional(self):
        original = make_scan(2, [0, 0, 1], [(0, 2, 1), (1, 2, 2)])
        original.live, original.composed = 3, {}
        proposal = first_jet_profile(original, range(3), audit=True)
        self.assertEqual(proposal['kappa'], 1)
        counter = [0]

        def count_work():
            counter[0] += 1

        completed = copy.deepcopy(original)
        _install(completed, [proposal], count_work)
        total_steps = counter[0]
        self.assertEqual(completed.live, 1)
        for allowance in range(total_steps):
            scan = copy.deepcopy(original)
            steps = [0]

            def interrupted():
                if steps[0] == allowance:
                    raise FirstJetBudget('injected installation limit')
                steps[0] += 1

            with self.assertRaises(FirstJetBudget):
                _install(scan, [proposal], interrupted)
            self.assertEqual(scan.__dict__, original.__dict__)

    def test_independent_complete_cube(self):
        rng = random.Random(29004)
        accepted = 0
        while accepted < 32:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 8))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            accepted += 1
            cube = Cube(diagram.pd)
            cube.check()
            expected = min(3, cube.homology_rank())
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            for budget in (None, 0, 120):
                result = first_jet_khovanov_decide(
                    diagram.pd, order=order, first_jet_max_work=budget,
                    check_d_squared=True, audit_jets=True)
                self.assertEqual(result['rank_capped'], expected)

    def test_actual_knots_random_orders_and_budget_fallback(self):
        rng = random.Random(29003)
        accepted = replacements = completed_with_expired_observer = 0
        while accepted < 60:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            accepted += 1
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            reference = FastScan(shape_cache=False)
            for index in order:
                reference.add_crossing(diagram.pd[index])
            expected = min(3, reference.total_rank())
            for allowance, replace, bounds in ((None, True, True), (0, True, True),
                                               (70, True, True), (None, False, True),
                                               (None, True, False)):
                result = first_jet_khovanov_decide(
                    diagram.pd, order=order, shape_cache=False,
                    first_jet_max_work=allowance, replacements=replace,
                    closure_bounds=bounds, audit_jets=True, check_d_squared=True)
                self.assertEqual(result['rank_capped'], expected)
                replacements += result['first_jet_stats']['replacements']
                completed_with_expired_observer += result['first_jet_stats']['exhausted']
                self.assertLessEqual(result['first_jet_stats']['max_gap'], diagram.crossings)
        self.assertGreater(replacements, 0)
        self.assertGreater(completed_with_expired_observer, 0)

    def test_limits_after_completed_replacements(self):
        diagram = Diagram.from_braid(9, list(range(1, 9)))
        order = list(range(diagram.crossings))
        reference = first_jet_khovanov_decide(diagram.pd, order=order,
                                             first_jet_max_work=None)
        self.assertEqual(reference['status'], 'UNKNOT')
        self.assertGreater(reference['first_jet_stats']['replacements'], 1)
        limit = reference['first_jet_stats']['work_units'] // 2
        limited = first_jet_khovanov_decide(diagram.pd, order=order,
                                           first_jet_max_work=limit)
        self.assertEqual(limited['status'], 'UNKNOT')
        self.assertTrue(limited['first_jet_stats']['exhausted'])
        self.assertGreater(limited['first_jet_stats']['replacements'], 0)
        self.assertLess(limited['first_jet_stats']['replacements'],
                        reference['first_jet_stats']['replacements'])
        self.assertEqual(reference['first_jet_stats']['max_gap'], 1)

    def test_validation_global_limits_and_empty_diagram(self):
        self.assertEqual(first_jet_khovanov_decide([])['status'], 'UNKNOT')
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for allowance in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                first_jet_khovanov_decide(diagram.pd, first_jet_max_work=allowance)
        with self.assertRaises(ValueError):
            first_jet_khovanov_decide(diagram.pd, order=[0, 0, 1])
        with self.assertRaises(ValueError):
            first_jet_khovanov_decide([(0, 1, 0, 1)])
        with self.assertRaises(ScanLimit):
            first_jet_khovanov_decide(diagram.pd, seconds=0, first_jet_max_work=0)
        with self.assertRaises(ScanLimit):
            first_jet_khovanov_decide(diagram.pd, max_objects=1)


if __name__ == '__main__':
    unittest.main()
