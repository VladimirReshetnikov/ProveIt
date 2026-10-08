"""Adversarial local replay checks, separate from the orbit producer tests."""

import copy
import random
import unittest

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import analyze_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate


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
        for key, replacement in (("version", 2), ("size", size + 1),
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


if __name__ == "__main__":
    unittest.main()
