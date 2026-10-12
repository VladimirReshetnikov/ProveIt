"""Literal component-incidence oracles, certificate mutations and shared caps."""
from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_incidence import (
    analyze_port_incidence, verify_port_incidence_certificate,
)
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.normal_surface_orbits import normal_arc_pairings
from normal_orbit_research.fixtures import layered_torus


def literal_histogram(size, pairs, ports):
    graph = [set() for _ in range(size)]
    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            graph[x].add(y)
            graph[y].add(x)
    unseen = set(range(size))
    histogram = [0] * (1 << len(ports))
    while unseen:
        start = unseen.pop()
        component, pending = {start}, [start]
        while pending:
            for y in graph[pending.pop()]:
                if y in unseen:
                    unseen.remove(y)
                    component.add(y)
                    pending.append(y)
        mask = 0
        for i, port in enumerate(ports):
            if any(lo <= x < hi for x in component for lo, hi in port):
                mask |= 1 << i
        histogram[mask] += 1
    return histogram


class IntervalIncidenceTests(unittest.TestCase):
    def test_random_literal_histograms_and_replay(self):
        rng = random.Random(261008482)
        for _ in range(250):
            size = rng.randrange(1, 41)
            pairs = []
            for _ in range(rng.randrange(10)):
                width = rng.randrange(1, size + 1)
                a, c = (rng.randrange(size - width + 1) for _ in range(2))
                pairs.append(IntervalPairing(a, a+width-1, c, c+width-1,
                                             bool(rng.getrandbits(1))))
            ports = [[sorted((rng.randrange(size+1), rng.randrange(size+1)))
                      for _ in range(rng.randrange(4))] for _ in range(rng.randrange(6))]
            result = analyze_port_incidence(size, pairs, ports, record_certificate=True)
            self.assertEqual(result['histogram'], literal_histogram(size, pairs, ports))
            self.assertTrue(verify_port_incidence_certificate(size, pairs, ports,
                                                              result['certificate']))

    def test_empty_and_huge_static_universes(self):
        for size, ports in ((0, []), (0, [[], [(0, 0)]]), (13, [])):
            result = analyze_port_incidence(size, [], ports, record_certificate=True)
            self.assertEqual(result['histogram'], [size] + [0] * ((1 << len(ports)) - 1))
            self.assertTrue(verify_port_incidence_certificate(size, [], ports,
                                                              result['certificate']))
        n = 1 << 16000
        ports = [[(0, n)], [(n // 2, 2*n)]]
        result = analyze_port_incidence(3*n, [], ports, record_certificate=True)
        self.assertEqual(result['histogram'], [n, n//2, n, n//2])
        encoded = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify_port_incidence_certificate(hex(3*n), [], json_safe(ports), encoded))

    def test_coincident_nested_and_empty_ports_reuse_proofs(self):
        ports = [[(0, 10)]] * 8
        result = analyze_port_incidence(20, [], ports, record_certificate=True)
        self.assertEqual(result['histogram'], [10] + [0]*254 + [10])
        self.assertEqual(result['stats']['orbit_queries'], 2)
        self.assertEqual(result['stats']['union_cache_hits'], 254)
        self.assertEqual(len(result['certificate']['proofs']), 1)
        ports = [[(0, i)] for i in range(1, 9)]
        result = analyze_port_incidence(20, [], ports, record_certificate=True)
        self.assertEqual(result['stats']['orbit_queries'], 9)
        self.assertEqual(result['histogram'], literal_histogram(20, [], ports))
        self.assertTrue(verify_port_incidence_certificate(20, [], ports, result['certificate']))

    def test_actual_normal_arc_components(self):
        for tetrahedra in range(1, 7):
            tri, coords = layered_torus(tetrahedra)
            for multiplicity in (1, 2, 3):
                scaled = [[v*multiplicity for v in row] for row in coords]
                size, pairs = normal_arc_pairings(tri, scaled)
                ports = [[(0, size//3)], [(size//4, size//2)],
                         [(size//2, size)], [(0, size//3)]]
                result = analyze_port_incidence(size, pairs, ports, record_certificate=True)
                self.assertEqual(result['histogram'], literal_histogram(size, pairs, ports))
                self.assertTrue(verify_port_incidence_certificate(size, pairs, ports,
                                                                  result['certificate']))

    def test_shared_budget_and_cancellation_never_publish_partial_histogram(self):
        pairs = [IntervalPairing(0, 8, 1, 9)]
        ports = [[(0, 3)], [(5, 7)]]
        full = analyze_port_incidence(10, pairs, ports, record_certificate=True)
        for cap in (0, 1, full['stats']['orbit_cycles'] - 1):
            limited = analyze_port_incidence(10, pairs, ports, max_cycles=cap,
                                             record_certificate=True)
            self.assertEqual(limited['status'], 'INCONCLUSIVE')
            self.assertNotIn('histogram', limited)
            self.assertNotIn('certificate', limited)
            self.assertLessEqual(limited['stats']['orbit_cycles'], cap)
        self.assertEqual(analyze_port_incidence(10, pairs, ports,
            max_cycles=full['stats']['orbit_cycles'])['histogram'], full['histogram'])
        class Stopped(RuntimeError):
            pass
        def stop():
            raise Stopped
        with self.assertRaises(Stopped):
            analyze_port_incidence(0, [], [], check=stop)
        with self.assertRaises(Stopped):
            verify_port_incidence_certificate(10, pairs, ports, full['certificate'], check=stop)

    def test_verifier_rejects_mutations_without_producer_or_inverse_transform(self):
        pairs = [IntervalPairing(0, 3, 8, 11)]
        ports = [[(0, 2)], [(3, 7)], [(0, 2)]]
        result = analyze_port_incidence(20, pairs, ports, record_certificate=True)
        cert = result['certificate']
        with patch('fastunknot.interval_incidence.count_orbits', side_effect=AssertionError), \
             patch('fastunknot.interval_incidence.analyze_port_incidence', side_effect=AssertionError):
            self.assertTrue(verify_port_incidence_certificate(20, pairs, ports, cert))
        mutations = []
        for key, value in [('version', 1), ('size', 21), ('ports', []),
                           ('orbit_count', True), ('proofs', []), ('query_indices', []),
                           ('histogram', [0]*8), ('base', None)]:
            bad = deepcopy(cert)
            bad[key] = value
            mutations.append(bad)
        bad = deepcopy(cert)
        bad['query_indices'][2] = bad['query_indices'][1]
        mutations.append(bad)
        bad = deepcopy(cert)
        bad['query_indices'][1] = True
        mutations.append(bad)
        bad = deepcopy(cert)
        bad['proofs'][0]['orbit_count'] += 1
        mutations.append(bad)
        bad = deepcopy(cert)
        bad['proofs'].append(deepcopy(bad['proofs'][0]))
        mutations.append(bad)
        for bad in mutations:
            self.assertFalse(verify_port_incidence_certificate(20, pairs, ports, bad))
        self.assertFalse(verify_port_incidence_certificate(20, pairs, ports[::-1][1:], cert))

    def test_validation_and_normalization(self):
        for size, ports, kwargs in ((True, [], {}), (-1, [], {}), (3, None, {}),
                (3, [[(0, 4)]], {}), (3, [[(1, False)]], {}),
                (3, [[], []], {'max_ports': 1}), (3, [], {'max_cycles': True}),
                (3, [], {'record_certificate': 1})):
            with self.assertRaises(ValueError):
                analyze_port_incidence(size, [], ports, **kwargs)
        result = analyze_port_incidence(10, [], [[(2, 4), (0, 3), (5, 5)]],
                                       record_certificate=True)
        self.assertEqual(result['histogram'], [6, 4])
        self.assertTrue(verify_port_incidence_certificate(10, [], [[(0, 4)]],
                                                          result['certificate']))


if __name__ == '__main__':
    unittest.main()
