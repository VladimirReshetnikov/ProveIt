"""Read-only certificate and exact API boundary tests; standard library only."""
import copy
from dataclasses import FrozenInstanceError
import hashlib
import json
import sys
from pathlib import Path
import unittest

from binary_exact import (Certificate, hit_time, quartic, step, validate_certificate,
                          verify_certificate, vertex_index, window_index)

CERTIFICATE = Path(__file__).with_name("binary-radius6-conservation-certificate.json")


class IntSubclass(int):
    pass


class ExactBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = CERTIFICATE.read_bytes()
        cls.fixture = json.loads(cls.raw)

    def fresh(self):
        return copy.deepcopy(self.fixture)

    def test_valid_certificate_and_immutable_snapshots(self):
        source = self.fresh()
        before = copy.deepcopy(source)
        result = validate_certificate(source)
        self.assertTrue(verify_certificate(source))
        self.assertEqual(source, before)
        self.assertIs(type(result.table), tuple)
        self.assertIs(type(result.potential), tuple)
        self.assertEqual(len(result.table), 8192)
        self.assertEqual(len(result.potential), 4096)
        source["potential_by_vertex"][0] += 123
        self.assertEqual(result.potential[0], before["potential_by_vertex"][0])
        with self.assertRaises(FrozenInstanceError):
            result.table = ()
        self.assertEqual(CERTIFICATE.read_bytes(), self.raw)

    def test_direct_certificate_construction_is_strictly_immutable(self):
        snapshot = validate_certificate(self.fresh())
        self.assertEqual(Certificate(snapshot.table, snapshot.potential), snapshot)
        for table, potential in ((list(snapshot.table), snapshot.potential),
                                 (snapshot.table, list(snapshot.potential))):
            with self.assertRaises(TypeError):
                Certificate(table, potential)
        for field, size in (("table", 8192), ("potential", 4096)):
            for invalid in (True, 0.0, [], IntSubclass(0)):
                values = {"table": snapshot.table, "potential": snapshot.potential}
                values[field] = (invalid,) + values[field][1:]
                with self.assertRaises(TypeError):
                    Certificate(**values)
            for length in (0, size - 1, size + 1):
                values = {"table": snapshot.table, "potential": snapshot.potential}
                values[field] = (0,) * length
                with self.assertRaises(ValueError):
                    Certificate(**values)
        for invalid in (-1, 2):
            with self.assertRaises(ValueError):
                Certificate((invalid,) + snapshot.table[1:], snapshot.potential)
        self.assertEqual(Certificate(snapshot.table, (-10 ** 1000,) * 4096).potential[0],
                         -10 ** 1000)

    def test_fixture_hash_and_every_local_window(self):
        self.assertEqual(hashlib.sha256(self.raw).hexdigest(),
                         "6c99365818697ddd83bdbf529e17756fffaf2eacd55763b235919523b0041699")
        table = validate_certificate(self.fresh()).table
        for word in range(8192):
            occupied = tuple(i - 6 for i in range(13) if (word >> i) & 1)
            self.assertEqual(table[word], int(0 in step(occupied)), word)

    def test_integer_metadata_types_and_values(self):
        for field in ("radius", "verified_edges", "verified_vertices"):
            for invalid in (True, False, 6.0, "6", None, IntSubclass(6)):
                with self.subTest(field=field, invalid=invalid):
                    data = self.fresh()
                    data[field] = invalid
                    with self.assertRaises(TypeError):
                        verify_certificate(data)
            for invalid in (-1, 0, 99999):
                data = self.fresh()
                data[field] = invalid
                with self.assertRaises(ValueError):
                    verify_certificate(data)

    def test_alphabet_strictness(self):
        for alphabet in ([False, True], [0.0, 1], [0, 1.0], [0, IntSubclass(1)]):
            data = self.fresh()
            data["alphabet"] = alphabet
            with self.assertRaises(TypeError):
                verify_certificate(data)
        for alphabet in ([0], [0, 1, 2], [1, 0], [0, 2]):
            data = self.fresh()
            data["alphabet"] = alphabet
            with self.assertRaises(ValueError):
                verify_certificate(data)

    def test_wrong_table_lengths_characters_and_containers(self):
        for bits in ("0" * 8191, "0" * 8193, "2" + "0" * 8191,
                     "\u0660" + "0" * 8191):
            data = self.fresh()
            data["rule_bits_indexed_by_window"] = bits
            with self.assertRaises(ValueError):
                verify_certificate(data)
        for bits in ([0] * 8192, b"0" * 8192, True):
            data = self.fresh()
            data["rule_bits_indexed_by_window"] = bits
            with self.assertRaises(TypeError):
                verify_certificate(data)

    def test_wrong_potential_lengths_types_and_identity(self):
        for size in (0, 4095, 4097):
            data = self.fresh()
            data["potential_by_vertex"] = [0] * size
            with self.assertRaises(ValueError):
                verify_certificate(data)
        for bad in (False, 0.0, "0", None, [], IntSubclass(0)):
            data = self.fresh()
            data["potential_by_vertex"][17] = bad
            with self.assertRaises(TypeError):
                verify_certificate(data)
        data = self.fresh()
        data["potential_by_vertex"][17] += 1
        with self.assertRaisesRegex(ValueError, "identity fails at word"):
            verify_certificate(data)
        data = self.fresh()
        bits = data["rule_bits_indexed_by_window"]
        data["rule_bits_indexed_by_window"] = str(1 - int(bits[0])) + bits[1:]
        with self.assertRaisesRegex(ValueError, "identity fails at word 0"):
            verify_certificate(data)

    def test_malformed_mutable_containers_and_schema(self):
        for bad in ([], (), {"potential_by_vertex": []}, None):
            with self.assertRaises((TypeError, ValueError)):
                verify_certificate(bad)
        data = self.fresh()
        data["extra"] = []
        with self.assertRaises(ValueError):
            verify_certificate(data)
        for field in ("potential_by_vertex", "alphabet"):
            data = self.fresh()
            data[field] = {0: 0}
            with self.assertRaises(TypeError):
                verify_certificate(data)
        for field in ("encoding", "potential_index_encoding", "verified_identity"):
            data = self.fresh()
            data[field] += " reversed"
            with self.assertRaises(ValueError):
                verify_certificate(data)
            data[field] = []
            with self.assertRaises(TypeError):
                verify_certificate(data)

    def test_arbitrary_integer_potential_offsets(self):
        for offset in (10 ** 1000, -(10 ** 1000)):
            data = self.fresh()
            data["potential_by_vertex"] = tuple(p + offset for p in data["potential_by_vertex"])
            self.assertTrue(verify_certificate(data))

    def test_explicit_little_endian_indexing(self):
        for encode, size in ((window_index, 13), (vertex_index, 12)):
            for i in range(size):
                bits = [0] * size
                bits[i] = 1
                before = bits[:]
                self.assertEqual(encode(bits), 1 << i)
                self.assertEqual(bits, before)
            self.assertEqual(encode((1,) * size), (1 << size) - 1)
            for invalid in (True, 1.0, IntSubclass(1)):
                with self.assertRaises(TypeError):
                    encode([invalid] + [0] * (size - 1))
            for invalid in (-1, 2):
                with self.assertRaises(ValueError):
                    encode([invalid] + [0] * (size - 1))
            for wrong in ([0] * (size - 1), [0] * (size + 1)):
                with self.assertRaises(ValueError):
                    encode(wrong)
            with self.assertRaises(TypeError):
                encode({0: 1})

    def test_natural_parameters_and_huge_exact_values(self):
        for function, valid in ((hit_time, [0, 0]), (quartic, [0, 0, 0])):
            for i in range(len(valid)):
                for invalid in (True, False, 0.0, "0", None, IntSubclass(0)):
                    args = valid[:]
                    args[i] = invalid
                    with self.assertRaises(TypeError):
                        function(*args)
                args = valid[:]
                args[i] = -1
                with self.assertRaises(ValueError):
                    function(*args)
        self.assertEqual(hit_time(0, 0), 0)
        self.assertEqual(hit_time(0, 1), 4)
        self.assertEqual(quartic(0, 0, 0), 0)
        x, k = 10 ** 1000, 10 ** 1200
        t = k * k + (2 * x + 3) * k
        self.assertIs(type(hit_time(x, k)), int)
        self.assertEqual(hit_time(x, k), t)
        self.assertEqual(quartic(x, t, k), 0)
        self.assertEqual(quartic(x, t + 1, k), 1)
        self.assertEqual(quartic(x, 0, k), t * t)

    def test_coordinate_types_duplicates_and_valid_immutability(self):
        for bad in (None, "01", {0: True}, (x for x in [0, 1]),
                    [[0], [1]], [True], [0.0], [IntSubclass(0)]):
            with self.assertRaises(TypeError):
                step(bad)
        with self.assertRaises(ValueError):
            step([0, 0])
        for constructor in (list, tuple, set, frozenset):
            source = constructor((-9, -8, 7))
            before = copy.deepcopy(source)
            result = step(source)
            self.assertEqual(result, frozenset((-8, -7, 7)))
            self.assertIs(type(result), frozenset)
            self.assertEqual(source, before)
        source = [-9, -8]
        result = step(source)
        source.append(100)
        self.assertEqual(result, frozenset((-8, -7)))
        huge = 10 ** 1200
        self.assertEqual(step([huge, huge + 2]), frozenset((huge - 1, huge + 1)))
        self.assertEqual(step([]), frozenset())
        self.assertEqual(step([-5]), frozenset((-5,)))

    def test_exact_return_times_without_producer_import(self):
        for x in range(5):
            occupied = frozenset((0, 3, 4, x + 7))
            expected = {hit_time(x, k) for k in range(10)}
            actual = set()
            for t in range(hit_time(x, 9) + 1):
                if occupied.intersection(range(5)) == frozenset((0, 3, 4)):
                    actual.add(t)
                self.assertEqual(len(occupied), 4)
                occupied = step(occupied)
            self.assertEqual(actual, expected)


if __name__ == "__main__":
    # Record separate normal/optimized runs only when their exact inputs agree.
    # Existing producer fixtures are read-only; this receipt belongs to this suite.
    directory = Path(__file__).resolve().parent
    fingerprint = {
        name: hashlib.sha256((directory / name).read_bytes()).hexdigest()
        for name in ("binary_exact.py", "test_exact_boundaries.py",
                     "binary-radius6-conservation-certificate.json")
    }
    fixture_before = CERTIFICATE.read_bytes()
    program = unittest.main(verbosity=2, exit=False)
    result = program.result
    fixture_unchanged = CERTIFICATE.read_bytes() == fixture_before
    passed = result.wasSuccessful() and fixture_unchanged
    receipt_path = directory / "exact-boundary-results.json"
    modes = {}
    if receipt_path.exists():
        try:
            old = json.loads(receipt_path.read_text())
            if old.get("source_sha256") == fingerprint:
                modes = old.get("modes", {})
        except (ValueError, AttributeError):
            pass
    modes["normal" if __debug__ else "optimized"] = {
        "status": "PASS" if passed else "FAIL",
        "groups_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skipped": len(result.skipped),
        "certificate_fixture_unchanged": fixture_unchanged,
    }
    both_pass = all(modes.get(mode, {}).get("status") == "PASS"
                    for mode in ("normal", "optimized"))
    receipt = {
        "status": "PASS" if both_pass else ("PARTIAL" if passed else "FAIL"),
        "source_sha256": fingerprint,
        "modes": modes,
        "coverage": {
            "de_bruijn_edges_per_verification": 8192,
            "local_windows_compared_per_mode": 8192,
            "potential_vertices": 4096,
            "maximum_test_integer_input_decimal_digits": 2401,
        },
        "scope": "Exact API boundary tests; supplement, not replacement for mathematical proofs.",
    }
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    sys.exit(0 if passed else 1)
