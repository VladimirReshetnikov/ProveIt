from __future__ import annotations
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from tm_audit import parse, congruence, simulate

class AuditTests(unittest.TestCase):
    def test_parser_rejects_partial_or_duplicate_tables(self):
        for text in ('0 0 0 R 0', '#! start 0\n0 0 0 R 0',
                     '#! start 0\n0 0 0 R 0\n0 0 0 L 0\n0 1 1 R 0'):
            with self.assertRaises(ValueError):
                parse(text)
    def test_equivalent_states_merge(self):
        _, t = parse('#! start 0\n0 0 0 R 1\n0 1 1 L 0\n1 0 0 R 0\n1 1 1 L 1')
        cls, _ = congruence(t)
        self.assertEqual(cls[0], cls[1])
    def test_halting_distinguishes_states(self):
        _, t = parse('#! start 0\n0 0 0 R 1\n0 1 1 L 0\n1 0 0 R 2\n1 1 1 L 1')
        cls, _ = congruence(t)
        self.assertNotEqual(cls[0], cls[1])
        self.assertTrue(simulate(0, t, 2)['halted'])
        self.assertFalse(simulate(0, t, 1)['halted'])
    def test_nonhalting_prefix_is_not_a_decision(self):
        _, t = parse('#! start 0\n0 0 1 R 0\n0 1 1 R 0')
        r = simulate(0, t, 100)
        self.assertFalse(r['halted'])
        self.assertEqual(r['ones'], 100)
        self.assertEqual(r['head'], 100)

if __name__ == '__main__':
    unittest.main()
