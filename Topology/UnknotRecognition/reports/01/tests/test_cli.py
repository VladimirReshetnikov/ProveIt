import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def run(*args, input_text=None):
    return subprocess.run([sys.executable, "-m", "unknot", *args], cwd=ROOT,
                          input=input_text, text=True, capture_output=True, timeout=20)


class CliTests(unittest.TestCase):
    def test_stdin_recognize_and_verify(self):
        result = run("recognize", "-", input_text='{"rows":[[0,1],[0,1]]}')
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertEqual(data["verdict"], "UNKNOT")
        verified = run("verify", "-", input_text=result.stdout)
        self.assertEqual(verified.returncode, 0, verified.stderr)
        self.assertTrue(json.loads(verified.stdout)["valid"])

    def test_file_output_and_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "knot.json"
            cert = Path(directory) / "cert.json"
            output = Path(directory) / "result.json"
            source.write_text('{"x":[0,1,2,3,4],"o":[2,3,4,0,1]}')
            result = run("recognize", str(source), "--certificate", str(cert),
                         "--output", str(output))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(output.read_text())["verdict"], "KNOTTED")
            verified = run("verify", str(cert), "--input", str(source))
            self.assertEqual(verified.returncode, 0, verified.stderr)

    def test_unknown_exit_code(self):
        result = run("recognize", "-", "--max-states", "1", "--no-determinant",
                     input_text='{"rows":[[0,1],[1,2],[0,2]]}')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(json.loads(result.stdout)["verdict"], "UNKNOWN")

    def test_invalid_input_exit_code(self):
        for text in ["not json", "{}", '{"rows":[[0,0],[0,1]]}']:
            result = run("recognize", "-", input_text=text)
            self.assertEqual(result.returncode, 1)
            self.assertTrue(result.stderr.startswith("error:"))

    def test_show_and_pattern(self):
        result = run("show", "-", input_text='{"rows":[[0,1],[0,1]]}')
        self.assertEqual(result.returncode, 0)
        self.assertIn("Vertical strands pass over", result.stdout)
        result = run("pattern", "examples/pattern_theta.json")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(json.loads(result.stdout)["essential"])

class NormalCliTests(unittest.TestCase):
    def test_normal_command(self):
        result = run("normal", "examples/solid_torus.json")
        self.assertEqual(result.returncode, 0, result.stderr)
        value = json.loads(result.stdout)
        self.assertEqual(value["first_betti_number"], 1)
        self.assertTrue(value["face_matching"])
        self.assertFalse(value["manifoldness_checked"])
