from __future__ import annotations
import itertools
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from restart_entropy import state_count, lex_rank, lex_unrank, audit_trace

COUNTS = {"ranked_vectors": 0, "complete_countdowns": 0}


class RestartTests(unittest.TestCase):
    def test_exhaustive_counts_ranks_and_inverse(self):
        for length in range(7):
            for cap in range(4):
                for support in range(length + 2):
                    vectors = [x for x in itertools.product(range(cap + 1), repeat=length)
                               if sum(y != 0 for y in x) <= support]
                    self.assertEqual(state_count(length, cap, support), len(vectors))
                    for rank, vector in enumerate(vectors):
                        self.assertEqual(lex_rank(vector, cap, support), rank)
                        self.assertEqual(lex_unrank(rank, length, cap, support), vector)
                        COUNTS['ranked_vectors'] += 1
                    report = audit_trace(reversed(vectors), cap, support)
                    self.assertEqual(report['observed_states'], report['states_bound_from_start'])
                    COUNTS['complete_countdowns'] += 1

    def test_binary_countdown_and_long_sparse_state(self):
        self.assertEqual(state_count(40, 1, 40), 2**40)
        self.assertEqual(state_count(1000, 1000, 1), 1000001)
        x = (1000,) + (0,) * 999
        self.assertEqual(lex_rank(x, 1000, 1), 1000000)

    def test_invalid_parameters_and_traces(self):
        for fn in (lambda: state_count(-1, 1, 1), lambda: state_count(1, -1, 1),
                   lambda: lex_rank((2,), 1, 1), lambda: lex_rank((1, 1), 1, 1),
                   lambda: lex_unrank(2, 1, 1, 1),
                   lambda: audit_trace([], 1, 1),
                   lambda: audit_trace([(1,), (1,)], 1, 1),
                   lambda: audit_trace([(0,), (1,)], 1, 1),
                   lambda: audit_trace([(1,), (0, 0)], 1, 1)):
            with self.assertRaises(ValueError):
                fn()
