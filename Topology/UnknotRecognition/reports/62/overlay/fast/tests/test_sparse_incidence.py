"""Focused differential, exhaustive and hostile-certificate tests (MIT-0).

Run in the repository with unittest discovery, or via experiments/run_tests.py
in the standalone delivery. Literal graph references never call AHT.
"""
import copy
import itertools
import json
import random
import sys
import unittest
from unittest.mock import patch

from fastunknot.interval_orbits import IntervalPairing, SignedPairing, count_orbits
from fastunknot.interval_incidence import analyze_port_incidence
from fastunknot.integer_codec import json_safe
from fastunknot.sparse_zeta import recover_nonnegative_zeta, RecoveryLimit
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as sparse
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify
from fastunknot.sparse_signed_incidence import analyze_signed_sparse_port_incidence as signed_sparse
from fastunknot.sparse_signed_incidence_verify import verify_signed_sparse_port_incidence_certificate as signed_verify


def literal_histogram(n, pairs, ports):
    """Independent explicit disjoint-set model, used only for small n."""
    parent = list(range(n))

    def find(x):
        while x != parent[x]:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def join(x, y):
        parent[find(x)] = find(y)

    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            join(x, y)
    groups = {}
    for x in range(n):
        root = find(x)
        groups.setdefault(root, 0)
        for bit, port in enumerate(ports):
            if any(lo <= x < hi for lo, hi in port):
                groups[root] |= 1 << bit
    histogram = {}
    for mask in groups.values():
        histogram[mask] = histogram.get(mask, 0) + 1
    return [[mask, value] for mask, value in sorted(histogram.items())]


def literal_signed(n, pairs, ports):
    """Independent labelled adjacency/BFS check, not the parity-cover formula."""
    graph = [[] for _ in range(n)]
    for item in pairs:
        p, parity = item.pairing, item.parity
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            graph[x].append((y, parity))
            graph[y].append((x, parity))
    labels, histogram = {}, {}
    for root in range(n):
        if root in labels:
            continue
        labels[root], stack, mask, bad = 0, [root], 0, False
        while stack:
            x = stack.pop()
            for i, port in enumerate(ports):
                if any(a <= x < b for a, b in port):
                    mask |= 1 << i
            for y, parity in graph[x]:
                value = labels[x] ^ parity
                if y in labels:
                    bad |= labels[y] != value
                else:
                    labels[y] = value
                    stack.append(y)
        histogram.setdefault(mask, [0, 0])[int(bad)] += 1
    return [[mask, *values] for mask, values in sorted(histogram.items())]


def random_case(rng, max_ports=6):
    n = rng.randrange(31)
    pairs = []
    for _ in range(rng.randrange(13) if n else 0):
        width = rng.randrange(1, n + 1)
        a, c = rng.randrange(n - width + 1), rng.randrange(n - width + 1)
        pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                     bool(rng.randrange(2))))
    ports = []
    for _ in range(rng.randrange(max_ports + 1)):
        port = []
        for _ in range(rng.randrange(4)):
            lo, hi = sorted((rng.randrange(n + 1), rng.randrange(n + 1)))
            port.append((lo, hi))
        ports.append(port)
    return n, pairs, ports


class GenericRecoveryTests(unittest.TestCase):
    def test_exhaustive_6654_nonnegative_histograms(self):
        cases = 0
        for r in range(4):
            for h in itertools.product(range(3), repeat=1 << r):
                def query(mask):
                    return sum(v for t, v in enumerate(h) if t & mask == t), mask
                terms, steps, stats = recover_nonnegative_zeta(
                    r, sum(h), query, record_witness=True)
                expected = [(t, v) for t, v in enumerate(h) if v]
                self.assertEqual(sorted(terms), expected)
                self.assertEqual(stats['logical_zeta_queries'], r * len(expected))
                previous = []
                for step in steps:
                    t, c = step['mask'], step['count']
                    known = lambda u: sum(v for s, v in previous if s & u == s)
                    self.assertEqual(query(t)[0], known(t) + c)
                    self.assertEqual({i for i, _, _ in step['zeros']},
                                     {i for i in range(r) if t & (1 << i)})
                    for i, u, _ in step['zeros']:
                        self.assertFalse(u & (1 << i))
                        self.assertEqual((t ^ (1 << i)) & u, t ^ (1 << i))
                        self.assertEqual(query(u)[0], known(u))
                    previous.append((t, c))
                cases += 1
        self.assertEqual(cases, 6654)

    def test_unknown_sparsity_and_large_weights(self):
        r, h = 80, {0: 1 << 500, 1 << 79: 7, (1 << 80) - 1: 1 << 300}
        terms, _, stats = recover_nonnegative_zeta(
            r, sum(h.values()), lambda u: (sum(v for t, v in h.items() if t & u == t), None))
        self.assertEqual(dict(terms), h)
        self.assertEqual(stats['logical_zeta_queries'], 240)

    def test_term_limit(self):
        with self.assertRaises(RecoveryLimit):
            recover_nonnegative_zeta(1, 2, lambda u: (1, None), max_terms=1)

    def test_invalid_oracle_value(self):
        for bad in (-1, 4, True, None, '2'):
            with self.subTest(bad=bad), self.assertRaises(ArithmeticError):
                recover_nonnegative_zeta(1, 2, lambda u: (bad, None))

    def test_nonnegativity_is_a_contract(self):
        # h(empty)=1, h({0})=-1 would have total zero: not an admissible oracle.
        terms, _, stats = recover_nonnegative_zeta(1, 0, lambda u: (1, None))
        self.assertEqual(terms, [])
        self.assertEqual(stats['logical_zeta_queries'], 0)

    def test_generic_invalid_parameters(self):
        for r, c in [(True, 2), (-1, 2), (1, True), (1, -1)]:
            with self.assertRaises(ValueError):
                recover_nonnegative_zeta(r, c, lambda u: (0, None))


class SparseIncidenceTests(unittest.TestCase):
    def test_1000_literal_graphs_and_300_dense_comparisons(self):
        rng = random.Random(261008490)
        for index in range(1000):
            n, pairs, ports = random_case(rng)
            result = sparse(n, pairs, ports, record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['histogram'], literal_histogram(n, pairs, ports))
            self.assertTrue(verify(n, pairs, ports, result['certificate']))
            self.assertLessEqual(result['stats']['orbit_queries'],
                                 1 + len(ports) * len(result['histogram']))
            if index < 300:
                dense = analyze_port_incidence(n, pairs, ports)
                self.assertEqual(result['histogram'],
                                 [[i, v] for i, v in enumerate(dense['histogram']) if v])

    def test_no_ports_and_empty_universe(self):
        for n in (0, 1, 100, 1 << 500):
            result = sparse(n, [], [], record_certificate=True)
            self.assertEqual(result['histogram'], [[0, n]] if n else [])
            self.assertTrue(verify(n, [], [], result['certificate']))

    def test_empty_coincident_nested_and_disjoint_ports(self):
        n = 40
        for ports in ([[]] * 12, [[(1, 20)]] * 12,
                      [[(0, i + 1)] for i in range(12)],
                      [[(2 * i, 2 * i + 1)] for i in range(12)]):
            result = sparse(n, [], ports, record_certificate=True)
            self.assertEqual(result['histogram'], literal_histogram(n, [], ports))
            self.assertTrue(verify(n, [], ports, result['certificate']))

    def test_128_ports_16000_bit_universe_and_hex_transport(self):
        n = 1 << 16000
        ports = [[(0, n // 2)]] * 128
        limit_before = sys.get_int_max_str_digits()
        result = sparse(n, [], ports, record_certificate=True)
        self.assertEqual(result['histogram'], [[0, n // 2], [(1 << 128) - 1, n // 2]])
        self.assertEqual(result['stats']['orbit_queries'], 2)
        cert = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify(n, [], ports, cert))
        self.assertEqual(sys.get_int_max_str_digits(), limit_before)

    def test_huge_periodic_and_reflection_systems(self):
        n = 1 << 500
        for pairs in ([IntervalPairing(0, n - 8, 7, n - 1)],
                      [IntervalPairing(0, n - 1, 0, n - 1, True)]):
            ports = [[(i, i + 1)] for i in range(16)]
            result = sparse(n, pairs, ports, record_certificate=True)
            self.assertEqual(result['orbit_count'], count_orbits(n, pairs).orbits)
            self.assertTrue(verify(n, pairs, ports, result['certificate']))

    def test_normalization_and_pair_rows(self):
        pairs = [[6, 9, 0, 3, -1]]
        ports = [[(4, 7), (0, 4), (1, 2), (7, 7)]]
        result = sparse(10, pairs, ports, record_certificate=True)
        self.assertTrue(verify(10, pairs, [[(0, 7)]], result['certificate']))

    def test_unmarked_term_and_completeness(self):
        result = sparse(10, [], [[(0, 3)]], record_certificate=True)
        self.assertEqual(result['histogram'], [[0, 7], [1, 3]])
        cert = copy.deepcopy(result['certificate'])
        cert['steps'].pop()
        cert['histogram'].pop()
        self.assertFalse(verify(10, [], [[(0, 3)]], cert))

    def test_exact_singleton_query_and_certificate_bounds(self):
        for r in range(1, 17):
            ports = [[(2 * i, 2 * i + 1)] for i in range(r)]
            result = sparse(2 * r + 1, [], ports, record_certificate=True)
            self.assertEqual(result['stats']['orbit_queries'], 1 + r * (r + 1) // 2)
            self.assertEqual(len(result['certificate']['proofs']), 2 * r - 1)
            self.assertEqual(len(result['histogram']), r + 1)

    def test_input_not_mutated(self):
        pairs, ports = [[0, 3, 4, 7, -1]], [[(0, 3), (1, 5)]]
        snapshot = copy.deepcopy((pairs, ports))
        sparse(8, pairs, ports, record_certificate=True)
        self.assertEqual((pairs, ports), snapshot)

    def test_gluing_obstruction(self):
        ports = [[(0, 2)], [(2, 4)]]
        first = [IntervalPairing(0, 1, 2, 3)]
        second = [IntervalPairing(0, 1, 2, 3, True)]
        self.assertEqual(sparse(4, first, ports)['histogram'], [[3, 2]])
        self.assertEqual(sparse(4, second, ports)['histogram'], [[3, 2]])
        attachment = [IntervalPairing(0, 1, 2, 3)]
        self.assertEqual(count_orbits(4, first + attachment).orbits, 2)
        self.assertEqual(count_orbits(4, second + attachment).orbits, 1)


class BudgetAndValidationTests(unittest.TestCase):
    def assert_unpublished(self, result):
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        for key in ('histogram', 'certificate', 'orbit_count'):
            self.assertNotIn(key, result)

    def test_zero_work_allowances(self):
        for key in ('max_cycles', 'max_orbit_queries', 'max_terms'):
            self.assert_unpublished(sparse(10, [], [[(0, 3)]], **{key: 0},
                                           record_certificate=True))

    def test_shared_cycle_budget_exact_boundary(self):
        ports = [[(0, 3)], [(2, 6)], [(7, 9)]]
        full = sparse(10, [], ports, record_certificate=True)
        limit = full['stats']['orbit_cycles']
        self.assertGreater(limit, 1)
        result = sparse(10, [], ports, max_cycles=limit, record_certificate=True)
        self.assertEqual(result['histogram'], full['histogram'])
        limited = sparse(10, [], ports, max_cycles=limit - 1, record_certificate=True)
        self.assert_unpublished(limited)
        self.assertEqual(limited['stats']['orbit_cycles'], limit - 1)

    def test_shared_query_budget_exact_boundary(self):
        ports = [[(0, 3)], [(2, 6)], [(7, 9)]]
        full = sparse(10, [], ports)
        q = full['stats']['orbit_queries']
        self.assertEqual(sparse(10, [], ports, max_orbit_queries=q)['histogram'], full['histogram'])
        self.assert_unpublished(sparse(10, [], ports, max_orbit_queries=q - 1))

    def test_callbacks_propagate_even_value_error(self):
        def stop():
            raise ValueError('caller cancellation')
        with self.assertRaisesRegex(ValueError, 'caller cancellation'):
            sparse(10, [], [], check=stop)
        cert = sparse(10, [], [], record_certificate=True)['certificate']
        with self.assertRaisesRegex(ValueError, 'caller cancellation'):
            verify(10, [], [], cert, check=stop)

    def test_invalid_inputs_and_bool_rejection(self):
        cases = [(True, [], []), (-1, [], []), (4, None, []), (4, [], None),
                 (4, [], [[(-1, 3)]]), (4, [], [[(0, 5)]]), (4, [], [[(True, 2)]]),
                 (4, [[0, 1, 2, 3, True]], []), (4, [[0, 2, 2, 3, 1]], []),
                 (4, [[0, 1, 2, 3, 0]], []), (4, [None], [])]
        for n, pairs, ports in cases:
            with self.subTest(case=(n, pairs, ports)):
                with self.assertRaises(ValueError):
                    sparse(n, pairs, ports)
                self.assertFalse(verify(n, pairs, ports, {}))
        for key in ('max_ports', 'max_terms', 'max_cycles', 'max_orbit_queries'):
            for value in (-1, True, 1.5):
                with self.assertRaises(ValueError):
                    sparse(4, [], [], **{key: value})


class SparseCertificateTests(unittest.TestCase):
    def setUp(self):
        self.n, self.pairs = 12, [IntervalPairing(0, 1, 10, 11)]
        self.ports = [[(0, 3)], [(2, 6)], [(6, 9)]]
        self.cert = sparse(self.n, self.pairs, self.ports,
                           record_certificate=True)['certificate']
        self.assertTrue(verify(self.n, self.pairs, self.ports, self.cert))

    def reject(self, cert):
        self.assertFalse(verify(self.n, self.pairs, self.ports, cert))

    def test_source_binding(self):
        self.assertFalse(verify(self.n + 1, self.pairs, self.ports, self.cert))
        self.assertFalse(verify(self.n, [], self.ports, self.cert))
        self.assertFalse(verify(self.n, self.pairs, list(reversed(self.ports)), self.cert))

    def test_mass_and_mask_mutations(self):
        for field, value in [('count', -1), ('count', True), ('count', 999),
                             ('mask', 1 << 20), ('mask', True)]:
            cert = copy.deepcopy(self.cert)
            cert['steps'][0][field] = value
            self.reject(cert)
        for field in ('orbit_count', 'size'):
            cert = copy.deepcopy(self.cert)
            cert[field] = True
            self.reject(cert)

    def test_missing_or_non_dominating_zero(self):
        step = next(i for i, item in enumerate(self.cert['steps']) if item['zeros'])
        for mode in ('missing', 'bad_mask', 'bad_bit', 'duplicate', 'bad_ref'):
            cert = copy.deepcopy(self.cert)
            zeros = cert['steps'][step]['zeros']
            if mode == 'missing': zeros.pop()
            if mode == 'bad_mask': zeros[0][1] |= 1 << zeros[0][0]
            if mode == 'bad_bit': zeros[0][0] = True
            if mode == 'duplicate': zeros.append(copy.deepcopy(zeros[0]))
            if mode == 'bad_ref': zeros[0][2] = len(cert['proofs'])
            self.reject(cert)

    def test_unused_duplicate_and_rebound_union_proofs(self):
        cert = copy.deepcopy(self.cert)
        cert['proofs'].append(copy.deepcopy(cert['proofs'][0]))
        self.reject(cert)
        cert = copy.deepcopy(self.cert)
        cert['proofs'][0]['union'] = [(0, self.n)]
        self.reject(cert)
        cert = copy.deepcopy(self.cert)
        cert['proofs'][0]['trace'] = copy.deepcopy(cert['base'])
        self.reject(cert)

    def test_truncated_orbit_proofs(self):
        for in_base in (True, False):
            cert = copy.deepcopy(self.cert)
            trace = cert['base'] if in_base else cert['proofs'][0]['trace']
            trace['operations'] = trace['operations'][:-1]
            self.reject(cert)

    def test_bad_histogram_and_duplicate_atoms(self):
        for kind in ('count', 'duplicate', 'reorder'):
            cert = copy.deepcopy(self.cert)
            if kind == 'count': cert['histogram'][0][1] += 1
            if kind == 'duplicate': cert['steps'].append(copy.deepcopy(cert['steps'][0]))
            if kind == 'reorder': cert['histogram'].reverse()
            self.reject(cert)

    def test_malformed_containers(self):
        for field in ('base', 'steps', 'proofs', 'histogram', 'ports'):
            for bad in (None, 1, True, 'bad'):
                cert = copy.deepcopy(self.cert)
                cert[field] = bad
                self.reject(cert)
        for bad in (None, [], 0, 'bad'):
            self.reject(bad)

    def test_producers_disabled_during_replay(self):
        def forbidden(*args, **kwargs):
            raise AssertionError('producer called from independent verifier')
        with patch('fastunknot.interval_orbits.count_orbits', forbidden), \
             patch('fastunknot.sparse_incidence.count_orbits', forbidden), \
             patch('fastunknot.sparse_incidence.recover_nonnegative_zeta', forbidden):
            self.assertTrue(verify(self.n, self.pairs, self.ports, self.cert))

    def test_json_roundtrip(self):
        cert = json.loads(json.dumps(json_safe(self.cert)))
        self.assertTrue(verify(self.n, self.pairs, self.ports, cert))


class SignedSparseTests(unittest.TestCase):
    def test_300_literal_parity_graphs(self):
        rng = random.Random(261008491)
        for _ in range(300):
            n, pairs, ports = random_case(rng, 5)
            signed = [SignedPairing(pair, rng.randrange(2)) for pair in pairs]
            result = signed_sparse(n, signed, ports, record_certificate=True)
            self.assertEqual(result['histogram'], literal_signed(n, signed, ports))
            self.assertTrue(signed_verify(n, signed, ports, result['certificate']))

    def test_parity_is_not_interval_reversal(self):
        pair = IntervalPairing(0, 2, 0, 2, True)
        for parity in (0, 1):
            signed = [SignedPairing(pair, parity)]
            result = signed_sparse(3, signed, [[(0, 3)]], record_certificate=True)
            self.assertEqual(result['histogram'], [[1, 2 - parity, parity]])
            self.assertTrue(signed_verify(3, signed, [[(0, 3)]], result['certificate']))

    def test_signed_source_and_histogram_binding(self):
        rows, ports = [[0, 1, 2, 3, 1, 1]], [[(0, 4)]]
        cert = signed_sparse(4, rows, ports, record_certificate=True)['certificate']
        wrong = copy.deepcopy(cert)
        wrong['histogram'][0][1] += 1
        self.assertFalse(signed_verify(4, rows, ports, wrong))
        wrong = copy.deepcopy(cert)
        wrong['signed_pairings'][0][5] = True
        self.assertFalse(signed_verify(4, rows, ports, wrong))
        self.assertFalse(signed_verify(4, [[0, 1, 2, 3, 1, 0]], ports, cert))

    def test_signed_shared_work_budgets(self):
        rows, ports = [[0, 1, 2, 3, 1, 1]], [[(0, 1)], [(3, 4)]]
        full = signed_sparse(4, rows, ports, record_certificate=True)
        for key, stat in [('max_cycles', 'orbit_cycles'),
                          ('max_orbit_queries', 'orbit_queries')]:
            limit = full['stats'][stat]
            self.assertEqual(signed_sparse(4, rows, ports, **{key: limit})['histogram'],
                             full['histogram'])
            incomplete = signed_sparse(4, rows, ports, **{key: limit - 1},
                                       record_certificate=True)
            self.assertEqual(incomplete['status'], 'INCONCLUSIVE')
            self.assertNotIn('histogram', incomplete)
            self.assertNotIn('certificate', incomplete)

    def test_signed_hex_and_independent_replay(self):
        n = 1 << 16000
        rows, ports = [[0, n - 1, 0, n - 1, 1, 1]], [[(0, n)]]
        cert = signed_sparse(n, rows, ports, record_certificate=True)['certificate']
        transported = json.loads(json.dumps(json_safe(cert)))
        with patch('fastunknot.sparse_signed_incidence.analyze_sparse_port_incidence',
                   side_effect=AssertionError('producer called')):
            self.assertTrue(signed_verify(n, rows, ports, transported))

    def test_signed_invalid_parity(self):
        for parity in (-1, 2, True, None):
            with self.assertRaises(ValueError):
                signed_sparse(4, [[0, 1, 2, 3, 1, parity]], [])
            self.assertFalse(signed_verify(4, [[0, 1, 2, 3, 1, parity]], [], {}))


if __name__ == '__main__':
    unittest.main()
