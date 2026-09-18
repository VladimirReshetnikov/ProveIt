import contextlib
import io
import json
import tempfile
from pathlib import Path
import unittest

from unknot_recognition.cli import main
from unknot_recognition.normal import solid_torus_example


class CLITests(unittest.TestCase):
    def run_cli(self, data, arguments):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'input.json'
            path.write_text(json.dumps(data), encoding='utf-8')
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main([arguments[0], str(path), *arguments[1:]])
            return code, json.loads(output.getvalue())

    def test_unknot_exit(self):
        code, result = self.run_cli({'pd': []}, ['recognize'])
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], 'UNKNOT')

    def test_nontrivial_exit(self):
        code, result = self.run_cli({'braid': {'strands': 2, 'word': [1, 1, 1]}}, ['recognize'])
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], 'NONTRIVIAL')

    def test_unknown_exit(self):
        data = {'braid': {'strands': 3, 'word': [1, 2] * 5}}
        code, result = self.run_cli(data, ['recognize', '--max-resolutions', '4'])
        self.assertEqual(code, 3)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertIsNone(result['is_unknot'])

    def test_invalid_exit(self):
        code, result = self.run_cli({'braid': {'strands': 2, 'word': [1, 1]}}, ['recognize'])
        self.assertEqual(code, 2)
        self.assertNotIn('is_unknot', result)

    def test_pattern(self):
        code, result = self.run_cli({'rotations': [[0, 0, 1], [1, 2, 2]]}, ['pattern'])
        self.assertEqual(code, 0)
        self.assertFalse(result['essential'])
        self.assertTrue(result['negative_witness_verified'])

    def test_normal(self):
        t = solid_torus_example()
        code, result = self.run_cli({'tetrahedra': t.tetrahedra}, ['normal'])
        self.assertEqual(code, 0)
        self.assertEqual(result['first_betti_number'], 1)
        self.assertEqual(result['surfaces'][0]['summary']['euler_characteristic'], 1)

    def test_output_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path, output = Path(tmp) / 'in.json', Path(tmp) / 'out.json'
            path.write_text('{"pd": []}', encoding='utf-8')
            self.assertEqual(main(['recognize', str(path), '--output', str(output)]), 0)
            self.assertEqual(json.loads(output.read_text())['status'], 'UNKNOT')

    def test_trace_replay(self):
        with tempfile.TemporaryDirectory() as tmp:
            path, saved = Path(tmp) / 'in.json', Path(tmp) / 'out.json'
            path.write_text('{"braid": {"strands": 2, "word": [1]}}', encoding='utf-8')
            self.assertEqual(main(['recognize', str(path), '--output', str(saved)]), 0)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = main(['verify-reductions', str(path), str(saved)])
            self.assertEqual(code, 0)
            self.assertTrue(json.loads(output.getvalue())['proves_unknot'])


if __name__ == '__main__':
    unittest.main()
