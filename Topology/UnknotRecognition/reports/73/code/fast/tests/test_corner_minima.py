"""Dynamic cached prefixes checked against independent literal dictionaries."""
import random
import unittest

from fastunknot.corner_minima import CornerMinimumIndex


class CornerMinimumTests(unittest.TestCase):
    def test_replenishes_beyond_thirteen(self):
        index = CornerMinimumIndex([(0, i, i) for i in range(60)], {0: 2})
        for first in (0, 12, 24):
            score = index.commit_edit(range(first, first+12), [])
            self.assertEqual(score['vertices'][0]['minimum_after'], first+12)
            self.assertEqual(index.prefix(0)[0], (first+12, first+12))
            self.assertTrue(index.verify_invariants())
        self.assertEqual(index.score_edit(range(36, 48), [])['vertices'][0]['minimum_after'], 48)

    def test_random_interleaved_updates_and_queries(self):
        rng = random.Random(104729)
        live = {i: (i % 4, rng.randrange(8)) for i in range(160)}
        weights = {i: 1+(i % 2) for i in range(4)}
        index = CornerMinimumIndex([(v, i, x) for i, (v, x) in live.items()], weights)
        fresh = 160
        for step in range(350):
            # Both singleton-sized and larger batch exclusions, including ties.
            removed = rng.sample(list(live), rng.randrange(1, 25))
            added = [(rng.randrange(4), fresh+i, rng.randrange(20))
                     for i in range(len(removed))]
            fresh += len(added)
            target = {i: item for i, item in live.items() if i not in removed}
            target.update({i: (v, x) for v, i, x in added})
            def sums(data):
                groups = {v: [x for vv, x in data.values() if vv == v] for v in weights}
                return (sum(weights[v]*min(a) for v, a in groups.items()),
                        sum(len(a)*min(a) for a in groups.values()))
            old, new = sums(live), sums(target)
            got = index.score_edit(removed, added)
            self.assertEqual((got['link_euler_delta'], got['link_piece_delta']),
                             (new[0]-old[0], new[1]-old[1]))
            committed = index.commit_edit(removed, added)
            self.assertEqual(got, committed)
            live = target
            self.assertTrue(index.verify_invariants())

    def test_collective_minimum_is_not_sum(self):
        index = CornerMinimumIndex([(0, 0, 0), (0, 1, 0), (0, 2, 7)], {0: 2})
        a = index.score_edit([0], [(0, 3, 5)])
        b = index.score_edit([1], [(0, 4, 5)])
        both = index.score_edit([0, 1], [(0, 3, 5), (0, 4, 5)])
        self.assertEqual(a['link_euler_delta']+b['link_euler_delta'], 0)
        self.assertEqual(both['link_euler_delta'], 10)

    def test_invalid_edits_leave_records_unchanged(self):
        index = CornerMinimumIndex([(0, 0, 3), (0, 1, 3)], {0: 1})
        original = dict(index.records)
        for removals, additions in (([2], []), ([0, 0], []), ([0, 1], []),
                                     ([], [(0, 0, 3)]), ([], [(1, 2, 3)])):
            with self.assertRaises(ValueError):
                index.commit_edit(removals, additions)
            self.assertEqual(index.records, original)

    def test_huge_weights_and_identity_ties(self):
        scale = 1 << 20000
        index = CornerMinimumIndex([(0, i, (i // 5)*scale) for i in range(50)], {0: 2})
        self.assertEqual(index.prefix(0)[:5], tuple((0, i) for i in range(5)))
        index.commit_edit(range(20), [])
        self.assertEqual(index.minimum(0), 4*scale)
        self.assertTrue(index.verify_invariants())


if __name__ == '__main__':
    unittest.main()
