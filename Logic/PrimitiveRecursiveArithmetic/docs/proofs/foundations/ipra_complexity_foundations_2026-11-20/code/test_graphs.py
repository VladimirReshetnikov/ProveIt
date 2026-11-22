"""Finite differential and adversarial checks, not formal proofs."""
import itertools
import unittest
from dataclasses import replace

from graphs import (
    CountRound, EnumerationTranscript, Graph, SavitchStats,
    canonical_nonreach_transcript, closure, least_path, linear_reach,
    savitch, savitch_node_bound, transcript_bit_bound, valid_path,
    verify_enumeration, verify_nonreach,
)


class GraphTests(unittest.TestCase):
    def test_all_graphs_through_three_vertices(self):
        checked_graphs = 0
        checked_pairs = 0
        for n in range(1, 4):
            level = (n - 1).bit_length()
            for mask in range(1 << (n * n)):
                graph = Graph(n, mask)
                expected = closure(graph)
                checked_graphs += 1
                for source in range(n):
                    linear = linear_reach(graph, source, n - 1)
                    self.assertEqual(linear, expected[source])
                    transcript = canonical_nonreach_transcript(graph, source)
                    for target in range(n):
                        stats = SavitchStats()
                        answer = savitch(graph, source, target, stats=stats)
                        self.assertEqual(answer, expected[source][target])
                        self.assertLessEqual(stats.max_frames, level + 1)
                        self.assertLessEqual(stats.nodes, savitch_node_bound(n, level))
                        self.assertEqual(
                            verify_nonreach(graph, source, target, transcript),
                            not expected[source][target],
                        )
                        witness = least_path(graph, source, target, n - 1)
                        self.assertEqual(witness is not None, expected[source][target])
                        if witness is not None:
                            self.assertTrue(valid_path(graph, source, target, n - 1, witness))
                        checked_pairs += 1
        self.assertEqual(checked_graphs, 530)
        self.assertEqual(checked_pairs, 4674)

    def test_savitch_each_level_means_bounded_path(self):
        # Directed chain 0->1->2->3->4: relevant path lengths are not powers of two.
        graph = Graph(5, sum(1 << (u * 5 + u + 1) for u in range(4)))
        for level in range(4):
            for source in range(5):
                expected = linear_reach(graph, source, 2 ** level)
                for target in range(5):
                    self.assertEqual(savitch(graph, source, target, level), expected[target])

    def test_corrupted_transcripts_are_rejected(self):
        graph = Graph(3, 1 << 1)  # 0->1; vertex 2 is unreachable from 0.
        good = canonical_nonreach_transcript(graph, 0)
        self.assertTrue(verify_nonreach(graph, 0, 2, good))
        self.assertFalse(verify_nonreach(graph, 0, 1, good))
        self.assertFalse(verify_nonreach(graph, 0, 2, replace(good, rounds=good.rounds[:-1])))
        self.assertFalse(verify_nonreach(graph, 0, 2, replace(good, final=EnumerationTranscript(()))))

        # Omit a reachable vertex while retaining the exact-count requirement.
        omitted = list(good.final.entries)
        omitted[1] = None
        self.assertFalse(verify_nonreach(
            graph, 0, 2, replace(good, final=EnumerationTranscript(tuple(omitted)))
        ))
        # Forge a path to the unreachable vertex and omit a true one.
        forged = ((0,), None, (0, 2))
        self.assertFalse(verify_nonreach(
            graph, 0, 2, replace(good, final=EnumerationTranscript(forged))
        ))
        # A path has the right endpoint but uses an out-of-range vertex.
        invalid = ((0,), (0, 3, 1), None)
        self.assertFalse(verify_nonreach(
            graph, 0, 2, replace(good, final=EnumerationTranscript(invalid))
        ))
        # Corrupt an intermediate round, testing count propagation rather than final checks alone.
        round0 = good.rounds[0]
        wrong_enum = EnumerationTranscript((None, None, None))
        bad_round0 = CountRound((wrong_enum,) + round0.targets[1:])
        self.assertFalse(verify_nonreach(
            graph, 0, 2, replace(good, rounds=(bad_round0,) + good.rounds[1:])
        ))

    def test_enumeration_exact_count_forces_all_reachable_marks(self):
        # All mark subsets and all counts on every three-vertex graph/source/depth.
        # Positive marks use genuine paths, so this isolates the counting lemma.
        for mask in range(1 << 9):
            graph = Graph(3, mask)
            for source in range(3):
                for depth in range(3):
                    paths = tuple(least_path(graph, source, v, depth) for v in range(3))
                    reachable = tuple(path is not None for path in paths)
                    correct_count = sum(reachable)
                    for marks in itertools.product((False, True), repeat=3):
                        if any(mark and path is None for mark, path in zip(marks, paths)):
                            continue
                        transcript = EnumerationTranscript(tuple(
                            path if mark else None for mark, path in zip(marks, paths)
                        ))
                        ok, _ = verify_enumeration(
                            graph, source, depth, correct_count, 0, transcript, False
                        )
                        self.assertEqual(ok, marks == reachable)

    def test_declared_bounds_and_invalid_inputs(self):
        for n in range(1, 20):
            self.assertGreater(transcript_bit_bound(n), 0)
            # A loose polynomial bit bound, not a runtime claim for generation.
            self.assertLessEqual(transcript_bit_bound(n), 4 * (n + 1) ** 5)
        for n, mask in ((0, 0), (1, -1), (1, 2)):
            with self.assertRaises(ValueError):
                Graph(n, mask)
        with self.assertRaises(ValueError):
            savitch(Graph(2, 0), 0, 2)
        with self.assertRaises(ValueError):
            savitch(Graph(2, 0), 0, 1, -1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
