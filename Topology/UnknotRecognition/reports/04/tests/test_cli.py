import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CliTests(unittest.TestCase):
    def call(self, *args, text=None):
        return subprocess.run([sys.executable, '-m', 'unknot', *args], cwd=ROOT,
                              input=text, text=True, capture_output=True, check=False)

    def test_unknot(self):
        p = self.call('recognize', 'examples/unknot_r2.json', '--verify-d2')
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(json.loads(p.stdout)['status'], 'UNKNOT')

    def test_trefoil(self):
        p = self.call('recognize', 'examples/trefoil.json')
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(json.loads(p.stdout)['status'], 'KNOTTED')

    def test_limit_exit_code(self):
        p = self.call('recognize', 'examples/trefoil.json', '--max-states', '1')
        self.assertEqual(p.returncode, 3)
        self.assertEqual(json.loads(p.stdout)['status'], 'UNKNOWN')

    def test_invalid_input(self):
        p = self.call('recognize', '-', text='{"pd": [[1, 1, 1, 1]]}')
        self.assertEqual(p.returncode, 2)
        self.assertEqual(json.loads(p.stderr)['status'], 'INVALID_INPUT')

    def test_missing_file(self):
        p = self.call('recognize', 'no-such-file.json')
        self.assertEqual(p.returncode, 2)

    def test_normalize(self):
        p = self.call('normalize', 'examples/figure_eight.json')
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(len(json.loads(p.stdout)['pd']), 4)

    def test_ball_pattern(self):
        p = self.call('pattern', 'examples/pattern_cube.json')
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertTrue(json.loads(p.stdout)['essential_on_assumed_ball'])

    def test_help_disclaims_bound(self):
        p = self.call('--help')
        self.assertEqual(p.returncode, 0)
        self.assertIn('NOT an n^O(log n)', ' '.join(p.stdout.split()))


if __name__ == '__main__':
    unittest.main()
