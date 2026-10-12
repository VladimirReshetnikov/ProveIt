import itertools
import unittest
from integration.column_cancellation_verify import private_column_schedule
from integration.apply import transform, git_blob
from cancellation import column_cancellation_plan


class IntegrationTests(unittest.TestCase):
    def test_fast_path_matches_private_schedules(self):
        for entries in itertools.product(range(3), repeat=6):
            counts = {r: {c: entries[3*r+c] for c in range(3) if entries[3*r+c]}
                      for r in range(2)}
            plan = column_cancellation_plan(counts)
            ok = private_column_schedule(list(counts.values()), plan['cancellations'], set(range(3)))
            self.assertEqual(ok, not plan['remaining_rows'])

    def test_legacy_nonprivate_goes_to_fallback(self):
        matrix = [{0: 1, 1: 1}, {0: 1}]
        self.assertFalse(private_column_schedule(matrix, [[0, 0], [1, 1]], {0, 1}))
        self.assertTrue(private_column_schedule(matrix, [[0, 1], [1, 0]], {0, 1}))

    def test_mutated_moves_rejected(self):
        matrix = [{0: 1}, {1: 1}]
        for moves in [[[0, 0]], [[0, 0], [0, 0]], [[False, 0], [1, 1]], [[0, 0], [1, 2]]]:
            self.assertFalse(private_column_schedule(matrix, moves, {0, 1}))

    def test_transform_targets_compile(self):
        fixtures = {
            'core_handlebody.py': 'from heapq import heappop, heappush\ndef f(counts, check):\n    planned = capped_cancellation_plan(counts, check=check)\n',
            'bundle_boundary_kernel.py': 'from collections import Counter\ndef f(rows, check):\n    planned = capped_cancellation_plan(rows, check=check)\n',
            'core_handlebody_verify.py': "from .integer_codec import certificate_equal\ndef f(matrix, moves, live_rows, live_columns, check, m, leaf):\n    if leaf:\n        moves = []\n    else:\n        matrix = [[row.get(c, 0) for c in range(m)] for row in matrix]\n",
        }
        for name, text in fixtures.items():
            compiled = transform(name, text)
            compile(compiled, name, 'exec')
            self.assertIn('column', compiled)
            with self.assertRaises(ValueError):
                transform(name, text.replace('planned = ', 'other = ') if 'planned = ' in text else '')

    def test_git_hash_is_content_sensitive(self):
        self.assertEqual(git_blob(b''), 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391')
        self.assertNotEqual(git_blob(b'x\n'), git_blob(b'x\r\n'))


if __name__ == '__main__':
    unittest.main(verbosity=2)
