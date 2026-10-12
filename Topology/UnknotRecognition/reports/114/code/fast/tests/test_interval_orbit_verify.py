"""Adversarial local replay checks, separate from the orbit producer tests."""

import copy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate


def analyze_orbits(size, pairings, *, record_trace=False):
    """Adapt the delivery's fixtures to the maintained public producer API."""
    pairs = []
    for raw in pairings:
        start, stop, sign, offset = [encoded_integer(raw[k])
                                     for k in ('start', 'stop', 'sign', 'offset')]
        if start == stop:
            continue
        images = sorted((sign * start + offset, sign * (stop - 1) + offset))
        pairs.append(IntervalPairing(start, stop - 1, *images, sign == -1))
    result = count_orbits(encoded_integer(size), pairs, periodic_rule='aht',
                          record_certificate=record_trace)
    return dict(orbit_count=result.orbits, certificate=result.certificate)


def pairing(a, b, c, d, sign=1):
    return {"start": a, "stop": b + 1, "sign": sign,
            "offset": c - a if sign == 1 else a + d}


def literal_count(size, pairings):
    parent = list(range(size))

    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for raw in pairings:
        for x in range(raw["start"], raw["stop"]):
            y = raw["sign"] * x + raw["offset"]
            parent[root(x)] = root(y)
    return len({root(x) for x in range(size)})


class TestIntervalOrbitVerifier(unittest.TestCase):
    def verify(self, size, pairs):
        result = analyze_orbits(size, pairs, record_trace=True)
        self.assertTrue(verify_orbit_certificate(size, pairs, result["certificate"]))
        return result["certificate"]

    def test_empty_and_static_universes(self):
        for size in (0, 1, 17, 1 << 600):
            with self.subTest(size_bits=size.bit_length()):
                cert = self.verify(size, [])
                self.assertEqual(cert["orbit_count"], size)

    def test_identity_reflections_and_disconnected_supports(self):
        pairs = [pairing(0, 0, 0, 0, -1), pairing(1, 1, 2, 2),
                 pairing(10, 10, 19, 19)]
        cert = self.verify(20, pairs)
        self.assertEqual(cert["orbit_count"], 18)

    def test_merger_retains_both_exterior_supports(self):
        # A merger confined to the first periodic hull would lose points 6,7.
        pairs = [pairing(0, 3, 2, 5), pairing(3, 6, 4, 7)]
        cert = self.verify(8, pairs)
        self.assertEqual(cert["orbit_count"], 1)
        self.assertIn("merge", {op["op"] for op in cert["operations"]})

    def test_reflection_center_is_preserved_as_an_orbit(self):
        for size in (5, 6, (1 << 600) + 1):
            pairs = [pairing(0, size - 1, 0, size - 1, -1)]
            cert = self.verify(size, pairs)
            self.assertEqual(cert["orbit_count"], (size + 1) // 2)
            self.assertIn("trim", {op["op"] for op in cert["operations"]})

    def test_independent_small_oracle(self):
        rng = random.Random(202610081)
        seen = set()
        for case in range(500):
            size = rng.randrange(1, 40)
            pairs = []
            for _ in range(rng.randrange(1, 9)):
                width = rng.randrange(1, size + 1)
                a, c = (rng.randrange(size - width + 1) for _ in range(2))
                pairs.append(pairing(a, a + width - 1, c, c + width - 1,
                                     rng.choice((-1, 1))))
            cert = self.verify(size, pairs)
            self.assertEqual(cert["orbit_count"], literal_count(size, pairs), case)
            seen.update(op["op"] for op in cert["operations"])
        self.assertEqual(seen, {"delete", "trim", "contract", "merge",
                               "transmit", "truncate"})

    def test_claim_and_binding_mutations(self):
        size = 21
        pairs = [pairing(0, 17, 3, 20), pairing(1, 16, 4, 19, -1)]
        cert = self.verify(size, pairs)
        for key, replacement in (("version", 5), ("size", size + 1),
                                 ("orbit_count", cert["orbit_count"] + 1),
                                 ("orbit_count", True), ("pairings", [])):
            damaged = copy.deepcopy(cert)
            damaged[key] = replacement
            self.assertFalse(verify_orbit_certificate(size, pairs, damaged), key)
        changed_input = copy.deepcopy(pairs)
        changed_input[0]["offset"] += 1
        self.assertFalse(verify_orbit_certificate(size, changed_input, cert))
        self.assertFalse(verify_orbit_certificate(size, pairs[::-1], cert))

    def test_incomplete_trace_is_rejected(self):
        pairs = [pairing(0, 19, 7, 26)]
        cert = self.verify(27, pairs)
        for length in range(len(cert["operations"])):
            damaged = copy.deepcopy(cert)
            damaged["operations"] = damaged["operations"][:length]
            self.assertFalse(verify_orbit_certificate(27, pairs, damaged))

    def test_illegal_local_operations(self):
        pairs = [pairing(0, 2, 3, 5)]
        cert = self.verify(6, pairs)
        invalid = [
            {"op": "delete", "index": 0},
            {"op": "delete", "index": True},
            {"op": "trim", "index": 0},
            {"op": "contract", "gaps": [[0, 5]]},
            {"op": "merge", "left": 0, "right": 0},
            {"op": "transmit", "transmitter": 0, "target": 0,
             "source_power": 0, "target_power": 1},
            {"op": "truncate", "index": 0, "new_size": 2},
            {"op": "truncate", "index": 0, "new_size": 6},
            {"op": "magic_orbit_count", "answer": 3},
            None,
        ]
        for event in invalid:
            damaged = copy.deepcopy(cert)
            damaged["operations"].insert(0, event)
            self.assertFalse(verify_orbit_certificate(6, pairs, damaged), event)

    def test_transmission_inverse_power_must_be_defined(self):
        pairs = [pairing(0, 15, 4, 19), pairing(8, 9, 12, 13)]
        cert = self.verify(20, pairs)
        damaged = copy.deepcopy(cert)
        damaged["operations"].insert(0, {
            "op": "transmit", "transmitter": 0, "target": 1,
            "source_power": 0, "target_power": 10 ** 100})
        self.assertFalse(verify_orbit_certificate(20, pairs, damaged))

    def test_suffix_cannot_delete_another_pairings_points(self):
        pairs = [pairing(0, 4, 5, 9), pairing(7, 7, 8, 8)]
        cert = self.verify(10, pairs)
        damaged = copy.deepcopy(cert)
        damaged["operations"].insert(0, {
            "op": "truncate", "index": 0, "new_size": 5})
        self.assertFalse(verify_orbit_certificate(10, pairs, damaged))

    def test_identity_cannot_be_truncated_away(self):
        pairs = [pairing(0, 0, 0, 0)]
        forged = {"version": 1, "size": 1, "pairings": [[0, 0, 0, 0, 1]],
                  "orbit_count": 0, "operations": [
                      {"op": "truncate", "index": 0, "new_size": 0}]}
        self.assertFalse(verify_orbit_certificate(1, pairs, forged))

    def test_hexadecimal_transport_and_empty_pairing(self):
        size = 1 << 5000
        pairs = [{"start": 0, "stop": size - 1, "sign": 1, "offset": 1},
                 {"start": size, "stop": size, "sign": -1, "offset": -size}]
        cert = self.verify(size, pairs)
        self.assertEqual(cert["orbit_count"], 1)
        self.assertTrue(verify_orbit_certificate(hex(size), json_safe(pairs),
                                                json_safe(cert)))

    def test_malformed_inputs_fail_without_producer_calls(self):
        cert = self.verify(0, [])
        for size, pairs, witness in ((True, [], cert), (-1, [], cert),
                                     (0, None, cert), (0, [], None),
                                     (0, [{}], cert), (0, [], {})):
            self.assertFalse(verify_orbit_certificate(size, pairs, witness))

    def test_interruptions_propagate(self):
        class Interrupted(RuntimeError):
            pass

        def stop():
            raise Interrupted("test cancellation")

        cert = self.verify(0, [])
        with self.assertRaises(Interrupted):
            verify_orbit_certificate(0, [], cert, check=stop)

    def test_sharp_merger_requires_version_two(self):
        pairs = [IntervalPairing(0, 3, 2, 5), IntervalPairing(2, 4, 5, 7)]
        result = count_orbits(8, pairs, record_certificate=True)
        self.assertTrue(verify_orbit_certificate(8, pairs, result.certificate))
        self.assertEqual(result.certificate['version'], 2)
        self.assertEqual(result.orbits, 1)
        damaged = copy.deepcopy(result.certificate)
        damaged['version'] = 1
        self.assertFalse(verify_orbit_certificate(8, pairs, damaged))
        # One fewer common point is insufficient, even in the new version.
        shifted = [pairs[0], IntervalPairing(3, 5, 6, 8)]
        forged = dict(version=2, size=9, orbit_count=1,
                      pairings=[[0, 3, 2, 5, 1], [3, 5, 6, 8, 1]],
                      operations=[{'op': 'merge', 'left': 0, 'right': 1},
                                  {'op': 'truncate', 'index': 0, 'new_size': 1},
                                  {'op': 'contract', 'gaps': [[0, 0]]}])
        self.assertFalse(verify_orbit_certificate(9, shifted, forged))

    def test_sharp_random_replay_preserves_untraced_results(self):
        rng = random.Random(261008481)
        for _ in range(1000):
            size = rng.randrange(1, 90)
            pairs = []
            for _ in range(rng.randrange(18)):
                width = rng.randrange(1, size + 1)
                a, c = (rng.randrange(size - width + 1) for _ in range(2))
                pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                             bool(rng.getrandbits(1))))
            result = count_orbits(size, pairs, record_certificate=True)
            plain = count_orbits(size, pairs)
            self.assertEqual((plain.orbits, plain.cycles, plain.stats),
                             (result.orbits, result.cycles, result.stats))
            self.assertIsNone(plain.certificate)
            rows = [[p.a, p.b, p.c, p.d, -1 if p.reverse else 1] for p in pairs]
            self.assertTrue(verify_orbit_certificate(size, rows, result.certificate))
            public = [pairing(*row) for row in rows]
            self.assertEqual(result.orbits, literal_count(size, public))

    def test_verifier_does_not_call_producer_and_transports_huge_powers(self):
        size = 1 << 16000
        pairs = [IntervalPairing(0, size - 2, 1, size - 1),
                 IntervalPairing(0, 0, size - 1, size - 1)]
        result = count_orbits(size, pairs, record_certificate=True)
        certificate = json.loads(json.dumps(json_safe(result.certificate)))
        with patch('fastunknot.interval_orbits.count_orbits', side_effect=AssertionError), \
             patch('fastunknot.interval_orbits._transmit', side_effect=AssertionError):
            self.assertTrue(verify_orbit_certificate(hex(size), pairs, certificate))
        powers = [e['target_power'] for e in result.certificate['operations']
                  if e['op'] == 'transmit']
        self.assertIn(size - 1, powers)
        self.assertLess(len(result.certificate['operations']), 10)

    def test_incomplete_runs_publish_no_certificate(self):
        pairs = [IntervalPairing(0, 8, 1, 9)]
        result = count_orbits(10, pairs, max_cycles=1, record_certificate=True)
        self.assertFalse(result.complete)
        self.assertIsNone(result.orbits)
        self.assertIsNone(result.certificate)
        with self.assertRaises(ValueError):
            count_orbits(0, [], record_certificate=1)

    def test_malformed_canonical_rows_and_booleans(self):
        pairs = [IntervalPairing(0, 1, 1, 2)]
        cert = count_orbits(3, pairs, record_certificate=True).certificate
        for rows in ([pairs[0]], [None], [{}], [[0, 1, 1, 2, True]],
                     [[0, 1, 1, 2]], [[1, 2, 0, 1, 1]]):
            damaged = copy.deepcopy(cert)
            damaged['pairings'] = rows
            self.assertFalse(verify_orbit_certificate(3, pairs, damaged))


if __name__ == "__main__":
    unittest.main()
