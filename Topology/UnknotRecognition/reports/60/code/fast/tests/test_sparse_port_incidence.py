"""Compare sparse weighted signatures with dense and literal component oracles."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot.interval_orbits import IntervalPairing
from fastunknot.interval_incidence import analyze_port_incidence
from fastunknot.sparse_port_incidence import sparse_port_incidence, verify_sparse_port_certificate


class SparsePortTests(unittest.TestCase):
    def test_random_dense_equivalence(self):
        rng = random.Random(261009102)
        for _ in range(250):
            size = rng.randrange(1, 31)
            pairs = []
            for _ in range(rng.randrange(7)):
                width = rng.randrange(1, size + 1)
                a, c = (rng.randrange(size - width + 1) for _ in range(2))
                pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                             bool(rng.randrange(2))))
            ports = []
            for _ in range(rng.randrange(6)):
                port = [sorted((rng.randrange(size + 1), rng.randrange(size + 1)))
                        for _ in range(rng.randrange(4))]
                ports.append(port)
            dense = analyze_port_incidence(size, pairs, ports)
            answer = sparse_port_incidence(size, pairs, ports, record_certificate=True)
            expected = [{'mask': mask, 'orbits': count}
                        for mask, count in enumerate(dense['histogram']) if count]
            self.assertEqual(answer['histogram'], expected)
            self.assertTrue(verify_sparse_port_certificate(size, pairs, ports,
                                                          answer['certificate']))

    def test_many_ports_and_huge_universe(self):
        scale, count = 2 ** 5000, 256
        ports = [[(j * scale, (j + 1) * scale)] for j in range(count)]
        answer = sparse_port_incidence(count * scale, [], ports, record_certificate=True)
        self.assertEqual(len(answer['histogram']), count)
        self.assertEqual(answer['histogram'],
                         [{'mask': 1 << j, 'orbits': scale} for j in range(count)])
        self.assertEqual(answer['stats']['orbit_queries'], 1)
        self.assertTrue(verify_sparse_port_certificate(count * scale, [], ports,
                                                      answer['certificate']))

    def test_no_ports_empty_ports_and_unmarked_components(self):
        for size in (0, 1, 10 ** 50):
            for ports in ([], [[]], [[], []]):
                answer = sparse_port_incidence(size, [], ports, record_certificate=True)
                self.assertEqual(answer['histogram'],
                                 [{'mask': 0, 'orbits': size}] if size else [])
                self.assertTrue(verify_sparse_port_certificate(size, [], ports,
                                                              answer['certificate']))

    def test_proof_replay_without_search_and_mutations(self):
        ports = [[(0, 4)], [(2, 7)]]
        answer = sparse_port_incidence(10, [], ports, record_certificate=True)
        proof = answer['certificate']
        with patch('fastunknot.weighted_orbits.count_orbits', side_effect=AssertionError):
            self.assertTrue(verify_sparse_port_certificate(10, [], ports, proof))
        for key, value in [('mask', 7), ('orbits', True), ('orbits', 500)]:
            bad = deepcopy(proof)
            bad['histogram'][0][key] = value
            self.assertFalse(verify_sparse_port_certificate(10, [], ports, bad))
        self.assertFalse(verify_sparse_port_certificate(11, [], ports, proof))
        self.assertFalse(verify_sparse_port_certificate(10, [], [[(0, 5)], [(2, 7)]], proof))

    def test_limits_and_callback_exceptions(self):
        ports = [[(0, 3)], [(5, 8)]]
        for kwargs in ({'max_cycles': 0}, {'max_weight_blocks': 0},
                       {'max_operations': 0}, {'max_output_records': 0}):
            answer = sparse_port_incidence(10, [], ports, **kwargs)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('histogram', answer)
        proof = sparse_port_incidence(10, [], ports, record_certificate=True)['certificate']
        class Cancel(ValueError):
            pass
        for stop in (1, 10, 30):
            calls = [0]
            def check():
                calls[0] += 1
                if calls[0] == stop:
                    raise Cancel('test cancellation')
            with self.assertRaises(Cancel):
                verify_sparse_port_certificate(10, [], ports, proof, check=check)

