"""Meaningful algebraic and hostile-certificate tests; no geometric claims."""

from __future__ import annotations

import ast
from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

try:
    from .produce import produce
    from .verify import CERT_SCHEMA, INPUT_SCHEMA, VerificationError, input_digest, validate_input, verify
except ImportError:
    from produce import produce
    from verify import CERT_SCHEMA, INPUT_SCHEMA, VerificationError, input_digest, validate_input, verify


def instance(c1=0, c2=0, c3=0, e1=0, e2=0, **values):
    dims = dict(c1=c1, c2=c2, c3=c3, e1=e1, e2=e2)
    data = {
        "schema": INPUT_SCHEMA,
        "dims": dims,
        "d2": [[0] * c2 for _ in range(c1)],
        "d3": [[0] * c3 for _ in range(c2)],
        "e2": [[0] * e2 for _ in range(e1)],
        "j1": [[0] * e1 for _ in range(c1)],
        "j2": [[0] * e2 for _ in range(c2)],
        "s": [0] * c2,
    }
    if "delta2" in values:
        values["e2"] = values.pop("delta2")
    data.update(values)
    return data


def random_instance(rng):
    # The upper identity block allows a nonzero commuting square.
    c1 = rng.randrange(4)
    tail = rng.randrange(5)
    c2, c3, e1, e2 = c1 + tail, rng.randrange(4), rng.randrange(4), rng.randrange(5)
    rand = lambda rows, cols: [[rng.randrange(-3, 4) for _ in range(cols)] for _ in range(rows)]
    d2 = [[int(i == j) for j in range(c2)] for i in range(c1)]
    delta2, j1 = rand(e1, e2), rand(c1, e1)
    top = [[sum(j1[i][k] * delta2[k][j] for k in range(e1)) for j in range(e2)]
           for i in range(c1)]
    return instance(
        c1, c2, c3, e1, e2,
        d2=d2,
        d3=[[0] * c3 for _ in range(c1)] + rand(tail, c3),
        delta2=delta2, j1=j1, j2=top + rand(tail, e2),
        s=[0] * c1 + [rng.randrange(-3, 4) for _ in range(tail)],
    )


class QuotientTests(unittest.TestCase):
    def assert_certificate(self, data, expected=None):
        cert = produce(data)
        verdict = verify(data, cert)
        if expected is not None:
            self.assertEqual(verdict, expected)
        return cert

    def test_all_empty(self):
        self.assert_certificate(instance(), "INSIDE_BUNDLE_IMAGE")

    def test_empty_dimension_combinations(self):
        for mask in range(32):
            dimensions = [int(mask & (1 << i) != 0) for i in range(5)]
            with self.subTest(dimensions=dimensions):
                self.assert_certificate(instance(*dimensions), "INSIDE_BUNDLE_IMAGE")

    def test_no_variables_nonzero_cycle(self):
        data = instance(c2=3, s=[0, -7, 2])
        self.assert_certificate(data, "OUTSIDE_BUNDLE_IMAGE")

    def test_rational_only_bundle_support(self):
        data = instance(c2=1, e2=1, j2=[[2]], s=[1])
        cert = self.assert_certificate(data, "INSIDE_BUNDLE_IMAGE")
        self.assertEqual((cert["q"], cert["b"]), (2, [1]))

    def test_rational_only_boundary_support(self):
        data = instance(c2=1, c3=1, d3=[[3]], s=[1])
        cert = self.assert_certificate(data, "INSIDE_BUNDLE_IMAGE")
        self.assertEqual((cert["q"], cert["a"]), (3, [1]))

    def test_nonunit_dual_evaluation(self):
        data = instance(c2=2, c3=1, d3=[[2], [1]], s=[0, 1])
        cert = self.assert_certificate(data, "OUTSIDE_BUNDLE_IMAGE")
        self.assertEqual(cert["q"], 2)

    def test_nonzero_bundle_coboundary_witness(self):
        # All bundle 2-chains have nonzero boundary unless they vanish.
        data = instance(c2=1, e1=1, e2=1, delta2=[[3]], j2=[[2]], s=[1])
        cert = self.assert_certificate(data, "OUTSIDE_BUNDLE_IMAGE")
        self.assertNotEqual(cert["U"], [0])

    def test_membership_requires_cycle_constraint(self):
        data = instance(c2=2, e1=1, e2=2, delta2=[[1, 1]], j2=[[1, 0], [0, 1]], s=[1, 0])
        self.assert_certificate(data, "OUTSIDE_BUNDLE_IMAGE")
        data["s"] = [1, -1]
        self.assert_certificate(data, "INSIDE_BUNDLE_IMAGE")

    def test_positive_certificate_rescalings(self):
        examples = [instance(c2=1, e2=1, j2=[[2]], s=[1]),
                    instance(c2=1, e1=1, e2=1, delta2=[[3]], j2=[[2]], s=[1])]
        for data in examples:
            cert = self.assert_certificate(data)
            for multiplier in (2, 17, 2**127):
                scaled = deepcopy(cert)
                scaled["q"] *= multiplier
                for key in ("a", "b") if cert["kind"] == "supported" else ("Y", "U"):
                    scaled[key] = [multiplier * x for x in scaled[key]]
                self.assertEqual(verify(data, scaled), verify(data, cert))

    def test_positive_surface_rescalings(self):
        rng = random.Random(9017)
        for _ in range(40):
            data = random_instance(rng)
            cert = self.assert_certificate(data)
            scaled = deepcopy(data)
            scaled["s"] = [13 * value for value in data["s"]]
            self.assertEqual(verify(data, cert), verify(scaled, produce(scaled)))

    def test_hostile_certificate_mutations(self):
        examples = [instance(c2=1, e2=1, j2=[[2]], s=[1]),
                    instance(c2=1, e1=1, e2=1, delta2=[[3]], j2=[[2]], s=[1])]
        for data in examples:
            cert = produce(data)
            mutations = []
            for bad_q in (0, -1, True, 1.0, "1", cert["q"] + 1):
                altered = deepcopy(cert)
                altered["q"] = bad_q
                mutations.append(altered)
            altered = deepcopy(cert)
            altered["input_sha256"] = "0" * 64
            mutations.append(altered)
            altered = deepcopy(cert)
            altered["extra"] = "untrusted"
            mutations.append(altered)
            altered = deepcopy(cert)
            altered["kind"] = "unknown"
            mutations.append(altered)
            for key in ("a", "b") if cert["kind"] == "supported" else ("Y", "U"):
                if not cert[key]:
                    continue
                for replacement in (True, 1.0, "1", cert[key][0] + 1):
                    altered = deepcopy(cert)
                    altered[key][0] = replacement
                    mutations.append(altered)
                altered = deepcopy(cert)
                altered[key].append(0)
                mutations.append(altered)
            for altered in mutations:
                with self.subTest(kind=cert["kind"], mutation=altered):
                    with self.assertRaises(VerificationError):
                        verify(data, altered)

    def test_stale_input_binding(self):
        data = instance(c2=1, e2=1, j2=[[2]], s=[1])
        cert = produce(data)
        altered = deepcopy(data)
        altered["s"] = [2]
        with self.assertRaises(VerificationError):
            verify(altered, cert)

    def test_forged_support_noncycle_is_rejected(self):
        data = instance(c2=1, e1=1, e2=1, delta2=[[1]], j2=[[1]], s=[1])
        forged = {"schema": CERT_SCHEMA, "input_sha256": input_digest(data),
                  "kind": "supported", "q": 1, "a": [], "b": [1]}
        with self.assertRaisesRegex(VerificationError, "e2\\*b"):
            verify(data, forged)

    def test_forged_dual_does_not_annihilate_boundaries(self):
        data = instance(c2=1, c3=1, d3=[[1]], s=[1])
        forged = {"schema": CERT_SCHEMA, "input_sha256": input_digest(data),
                  "kind": "outside", "q": 1, "Y": [1], "U": []}
        with self.assertRaisesRegex(VerificationError, "Y\\*d3"):
            verify(data, forged)

    def test_forged_dual_does_not_annihilate_bundle_cycles(self):
        data = instance(c2=1, e2=1, j2=[[1]], s=[1])
        forged = {"schema": CERT_SCHEMA, "input_sha256": input_digest(data),
                  "kind": "outside", "q": 1, "Y": [1], "U": []}
        with self.assertRaisesRegex(VerificationError, "restriction"):
            verify(data, forged)

    def test_invalid_chain_complex(self):
        data = instance(c1=1, c2=1, c3=1, d2=[[1]], d3=[[1]])
        with self.assertRaisesRegex(VerificationError, "d2\\*d3"):
            produce(data)

    def test_invalid_commuting_square(self):
        data = instance(c1=1, c2=1, e1=1, e2=1, d2=[[1]], j2=[[1]])
        with self.assertRaisesRegex(VerificationError, "chain-map"):
            produce(data)

    def test_invalid_candidate_cycle(self):
        data = instance(c1=1, c2=1, d2=[[1]], s=[1])
        with self.assertRaisesRegex(VerificationError, "not a relative cycle"):
            produce(data)

    def test_strict_input_types_and_shapes(self):
        data = instance(c1=1, c2=1, c3=1, e1=1, e2=1)
        for bad in (True, 1.0, "1", -1):
            altered = deepcopy(data)
            altered["dims"]["c1"] = bad
            with self.assertRaises(VerificationError):
                validate_input(altered)
        for key in ("d2", "d3", "e2", "j1", "j2"):
            for bad in (True, 1.0, "0"):
                altered = deepcopy(data)
                altered[key][0][0] = bad
                with self.assertRaises(VerificationError):
                    validate_input(altered)
            altered = deepcopy(data)
            altered[key][0].append(0)
            with self.assertRaises(VerificationError):
                validate_input(altered)
        for bad in (None, {}, [], "invalid"):
            with self.assertRaises(VerificationError):
                validate_input(bad)

    def test_large_integer_data(self):
        huge = 2**2048 + 17
        data = instance(c2=2, c3=1, d3=[[huge], [1]], s=[0, 1])
        self.assert_certificate(data, "OUTSIDE_BUNDLE_IMAGE")

    def test_deterministic_and_json_roundtrip(self):
        data = instance(c2=2, e1=1, e2=2, delta2=[[2, 3]], j2=[[5, 1], [2, 4]], s=[1, 1])
        cert = produce(data)
        self.assertEqual(cert, produce(deepcopy(data)))
        self.assertEqual(verify(data, cert), verify(json.loads(json.dumps(data)), json.loads(json.dumps(cert))))

    def test_producer_does_not_mutate_input(self):
        rng = random.Random(991)
        for _ in range(20):
            data = random_instance(rng)
            original = deepcopy(data)
            self.assert_certificate(data)
            self.assertEqual(data, original)

    def test_verifier_is_independent(self):
        source = Path(__file__).with_name("verify.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        imported = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                imported.append(node.module or "")
        self.assertFalse(any(name.endswith("produce") or name == "fractions" for name in imported))

    def test_cli_roundtrip(self):
        data = instance(c2=1, e1=1, e2=1, delta2=[[3]], j2=[[2]], s=[1])
        here = Path(__file__).parent
        with tempfile.TemporaryDirectory() as tmp:
            input_file, cert_file = Path(tmp) / "input.json", Path(tmp) / "certificate.json"
            input_file.write_text(json.dumps(data), encoding="utf-8")
            first = subprocess.run([sys.executable, str(here / "produce.py"), str(input_file), "-o", str(cert_file)],
                                   capture_output=True, text=True)
            self.assertEqual(first.returncode, 0, first.stderr)
            second = subprocess.run([sys.executable, str(here / "verify.py"), str(input_file), str(cert_file)],
                                    capture_output=True, text=True)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(json.loads(second.stdout)["verdict"], "OUTSIDE_BUNDLE_IMAGE")

    def test_cli_16384_bit_roundtrip_with_explicit_decimal_limit_setting(self):
        # Both the input coefficient and the support denominator exceed the
        # default CPython decimal conversion limit.  Generate and inspect
        # those JSON files in subprocesses with the documented launch setting.
        here = Path(__file__).parent
        environment = dict(os.environ, PYTHONINTMAXSTRDIGITS="0")
        setup = """
import json, sys
from pathlib import Path
large = (1 << 16383) + 1
data = {
    "schema": "relative-chain-pair-v1",
    "dims": {"c1": 0, "c2": 1, "c3": 0, "e1": 0, "e2": 1},
    "d2": [], "d3": [[]], "e2": [], "j1": [],
    "j2": [[large]], "s": [1],
}
Path(sys.argv[1]).write_text(json.dumps(data), encoding="utf-8")
"""
        inspect = """
import json, sys
from pathlib import Path
certificate = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert certificate["q"] == (1 << 16383) + 1
assert certificate["q"].bit_length() == 16384
assert certificate["a"] == [] and certificate["b"] == [1]
"""
        with tempfile.TemporaryDirectory() as tmp:
            input_file, cert_file = Path(tmp) / "input.json", Path(tmp) / "certificate.json"
            commands = [
                [sys.executable, "-c", setup, str(input_file)],
                [sys.executable, str(here / "produce.py"), str(input_file), "-o", str(cert_file)],
                [sys.executable, str(here / "verify.py"), str(input_file), str(cert_file)],
                [sys.executable, "-c", inspect, str(cert_file)],
            ]
            for index, command in enumerate(commands):
                result = subprocess.run(command, capture_output=True, text=True, env=environment)
                self.assertEqual(result.returncode, 0, result.stderr)
                if index == 2:
                    self.assertEqual(json.loads(result.stdout)["verdict"], "INSIDE_BUNDLE_IMAGE")

    def test_random_instances_verify(self):
        rng = random.Random(260712)
        counts = {"INSIDE_BUNDLE_IMAGE": 0, "OUTSIDE_BUNDLE_IMAGE": 0}
        for _ in range(400):
            data = random_instance(rng)
            counts[verify(data, produce(data))] += 1
        self.assertGreater(counts["INSIDE_BUNDLE_IMAGE"], 100)
        self.assertGreater(counts["OUTSIDE_BUNDLE_IMAGE"], 100)

    @unittest.skipUnless(importlib.util.find_spec("sympy"), "optional SymPy oracle is unavailable")
    def test_random_oracle_rank_comparison(self):
        from sympy import Matrix

        rng = random.Random(145827)
        for index in range(250):
            data = random_instance(rng)
            d = data["dims"]
            rows, cols = d["c2"] + d["e1"], d["c3"] + d["e2"]
            block = [data["d3"][i] + data["j2"][i] for i in range(d["c2"])]
            block += [[0] * d["c3"] + row for row in data["e2"]]
            flat = [value for row in block for value in row]
            matrix = Matrix(rows, cols, flat)
            rhs = Matrix(rows, 1, data["s"] + [0] * d["e1"])
            supported = matrix.rank() == matrix.row_join(rhs).rank()
            expected = "INSIDE_BUNDLE_IMAGE" if supported else "OUTSIDE_BUNDLE_IMAGE"
            with self.subTest(index=index):
                self.assert_certificate(data, expected)


if __name__ == "__main__":
    unittest.main()
