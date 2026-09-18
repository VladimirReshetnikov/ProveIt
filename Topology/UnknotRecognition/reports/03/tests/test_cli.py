import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def run(args, obj=None, raw=None):
    result = subprocess.run([sys.executable, '-m', 'unknot_lab', *args], cwd=ROOT,
                            input=raw if raw is not None else json.dumps(obj),
                            text=True, capture_output=True, timeout=20)
    return result.returncode, json.loads(result.stdout)


class CliTests(unittest.TestCase):
    def test_empty_knot(self):
        code, result = run(['recognize', '-'], {'pd': []})
        self.assertEqual(code, 0)
        self.assertTrue(result['is_unknot'])

    def test_exact_nontrivial(self):
        code, result = run(['recognize', '-', '--no-filter', '--check-d2'],
                           {'braid': {'strands': 3, 'word': [1, 2] * 5}})
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], 'nontrivial')
        self.assertEqual(result['reduced_rank_f2'], 7)
        self.assertTrue(result['d_squared_checked'])

    def test_unknown_is_not_no(self):
        code, result = run(['recognize', '-', '--max-states', '1'],
                           {'braid': {'strands': 3, 'word': [1, 2]}})
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'unknown')
        self.assertIsNone(result['is_unknot'])

    def test_unlimited_overrides_resource_settings(self):
        code, result = run(['recognize', '-', '--max-states', '1', '--unlimited'],
                           {'braid': {'strands': 3, 'word': [1, 2]}})
        self.assertEqual(code, 0)
        self.assertTrue(result['is_unknot'])

    def test_invalid_inputs(self):
        for obj in [None, {'pd': [[1, 2, 1, 2]]},
                    {'braid': {'strands': 2, 'word': [1, 1]}}]:
            code, result = run(['recognize', '-'], obj)
            self.assertEqual(code, 3)
            self.assertEqual(result['status'], 'invalid-input')
        code, result = run(['recognize', '-'], raw='{not json')
        self.assertEqual(code, 3)
        self.assertIsNone(result['is_unknot'])

    def test_missing_file(self):
        code, result = run(['recognize', str(ROOT / 'not-a-real-file.json')])
        self.assertEqual(code, 3)
        self.assertEqual(result['status'], 'invalid-input')

    def test_conditional_bound(self):
        code, result = run(['bound', '2', '3'])
        self.assertEqual(code, 0)
        self.assertEqual(result['phase_bound'], 27)
        self.assertEqual(result['visit_bound'], 81)
        self.assertTrue(result['conditional_only'])
        self.assertFalse(result['establishes_unknot_runtime'])

    def test_pattern_and_witness(self):
        name = str(ROOT / 'examples' / 'pattern_prism.json')
        code, result = run(['pattern', name])
        self.assertEqual(code, 0)
        self.assertFalse(result['essential'])
        with tempfile.TemporaryDirectory() as directory:
            cert = Path(directory) / 'certificate.json'
            cert.write_text(json.dumps(result))
            code, check = run(['verify-pattern', name, str(cert)])
            self.assertEqual(code, 0)
            self.assertTrue(check['accepted'])
            cert.write_text('{}')
            code, check = run(['verify-pattern', name, str(cert)])
            self.assertEqual(code, 3)
            self.assertFalse(check['accepted'])


if __name__ == '__main__':
    unittest.main()
