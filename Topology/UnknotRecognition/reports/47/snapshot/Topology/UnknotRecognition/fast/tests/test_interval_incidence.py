"""Literal graph-orbit checks for compressed Boolean port-incidence counts."""

import copy
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_incidence import (
    analyze_port_incidence, verify_port_incidence_certificate,
)
from fastunknot.interval_orbits import OrbitLimitExceeded


def literal_histogram(size, pairings, ports):
    parent = list(range(size))

    def root(x):
        while x != parent[x]:
            x = parent[x]
        return x

    for pairing in pairings:
        for x in range(pairing["start"], pairing["stop"]):
            y = pairing["sign"] * x + pairing["offset"]
            parent[root(x)] = root(y)
    masks = {root(x): 0 for x in range(size)}
    for bit, port in enumerate(ports):
        for lo, hi in port:
            for x in range(lo, hi):
                masks[root(x)] |= 1 << bit
    histogram = [0] * (1 << len(ports))
    for mask in masks.values():
        histogram[mask] += 1
    return histogram


class TestIntervalIncidence(unittest.TestCase):
    def analyze(self, size, pairs, ports, **kwargs):
        answer = analyze_port_incidence(size, pairs, ports, record_trace=True, **kwargs)
        self.assertTrue(verify_port_incidence_certificate(
            size, pairs, ports, answer["certificate"]))
        return answer

    def test_empty_universe_and_no_ports(self):
        self.assertEqual(self.analyze(0, [], []) ["histogram"], [0])
        self.assertEqual(self.analyze(5, [], []) ["histogram"], [5])
        self.assertEqual(self.analyze(0, [], [[], [[0, 0]]])["histogram"], [0] * 4)

    def test_disjoint_and_overlapping_marks(self):
        ports = [[[0, 5]], [[3, 7]], [[1, 2], [8, 10]]]
        result = self.analyze(12, [], ports)
        self.assertEqual(result["histogram"], literal_histogram(12, [], ports))
        self.assertEqual(result["histogram"][0], 3)

    def test_incidence_uses_entire_orbits(self):
        pairs = [{"start": 0, "stop": 15, "sign": 1, "offset": 5}]
        ports = [[[1, 2]], [[11, 12]], [[4, 5]]]
        result = self.analyze(20, pairs, ports)
        self.assertEqual(result["histogram"], [3, 0, 0, 1, 1, 0, 0, 0])

    def test_duplicate_and_empty_ports(self):
        ports = [[[0, 8]], [[0, 3], [3, 8], [8, 8]], []]
        result = self.analyze(10, [], ports)
        self.assertEqual(result["histogram"], [2, 0, 0, 8, 0, 0, 0, 0])
        self.assertIsNone(result["certificate"]["queries"][4])

    def test_seeded_literal_graph_comparisons(self):
        rng = random.Random(202610082)
        for case in range(180):
            size, port_count = rng.randrange(1, 31), rng.randrange(0, 5)
            pairs = []
            for _ in range(rng.randrange(0, 8)):
                width = rng.randrange(1, size + 1)
                start, image = (rng.randrange(size - width + 1) for _ in range(2))
                sign = rng.choice((-1, 1))
                offset = image - start if sign == 1 else image + width - 1 + start
                pairs.append({"start": start, "stop": start + width,
                              "sign": sign, "offset": offset})
            ports = []
            for _ in range(port_count):
                intervals = []
                for _ in range(rng.randrange(0, 4)):
                    lo, hi = sorted(rng.randrange(size + 1) for _ in range(2))
                    intervals.append([lo, hi])
                ports.append(intervals)
            result = self.analyze(size, pairs, ports)
            expected = literal_histogram(size, pairs, ports)
            self.assertEqual(result["histogram"], expected, case)
            for mask, observed in enumerate(result["touched_counts"]):
                self.assertEqual(observed, sum(number for sig, number in enumerate(expected)
                                                if sig & mask), (case, mask))

    def test_huge_binary_orbits_and_transport(self):
        quarter = 1 << 5000
        period, size = 4 * quarter, 20 * quarter
        pairs = [{"start": 0, "stop": size - period, "sign": 1, "offset": period}]
        ports = [[[0, 2 * quarter]], [[quarter, 3 * quarter]]]
        answer = self.analyze(size, pairs, ports)
        self.assertEqual(answer["histogram"], [quarter] * 4)
        self.assertTrue(verify_port_incidence_certificate(
            hex(size), json_safe(pairs), json_safe(ports), json_safe(answer["certificate"])))

    def test_verifier_does_not_call_the_orbit_producer(self):
        ports = [[[0, 7]], [[4, 9]]]
        answer = self.analyze(12, [], ports)
        with patch("fastunknot.interval_incidence.analyze_orbits",
                   side_effect=AssertionError("producer invoked by verifier")):
            self.assertTrue(verify_port_incidence_certificate(
                12, [], ports, answer["certificate"]))

    def test_histogram_and_mark_tampering(self):
        ports = [[[0, 5]], [[3, 7]]]
        answer = self.analyze(10, [], ports)
        cert = answer["certificate"]
        for field, value in (("histogram", [2, 2, 2, 4]), ("orbit_count", 9),
                             ("queries", cert["queries"][:-1]),
                             ("ports", [[[0, 4]], [[3, 7]]])):
            damaged = copy.deepcopy(cert)
            damaged[field] = value
            self.assertFalse(verify_port_incidence_certificate(10, [], ports, damaged), field)
        self.assertFalse(verify_port_incidence_certificate(10, [], ports[::-1], cert))
        damaged = copy.deepcopy(cert)
        damaged["queries"][1]["orbit_count"] += 1
        self.assertFalse(verify_port_incidence_certificate(10, [], ports, damaged))

    def test_port_limits_and_malformed_marks(self):
        for ports in ([[]] * 13, [[[0, 2]]], [[[True, 1]]], [None], None):
            with self.assertRaises(ValueError):
                analyze_port_incidence(1, [], ports)
        with self.assertRaises(ValueError):
            analyze_port_incidence(1, [], [[]], max_ports=0)
        with self.assertRaises(ValueError):
            analyze_port_incidence(1, [], [], max_ports=True)
        with self.assertRaises(ValueError):
            analyze_port_incidence(1, [], [], record_trace=1)

    def test_cycle_limit_and_callback_propagation(self):
        with self.assertRaises(OrbitLimitExceeded):
            analyze_port_incidence(5, [], [], max_cycles=0)

        def stop():
            raise ValueError("caller cancellation remains an exception")

        with self.assertRaisesRegex(ValueError, "caller cancellation"):
            analyze_port_incidence(1, [], [], check=stop)
        with self.assertRaisesRegex(ValueError, "caller cancellation"):
            verify_port_incidence_certificate(1, [], [], {}, check=stop)


if __name__ == "__main__":
    unittest.main()
