"""Topology-preserving endpoint descent and adversarial certificate replay."""
import copy
import random
import unittest

from fastunknot.braid_reduction import singleton_reduce, verify_singleton_reduction
from fastunknot.diagram import Diagram
from fastunknot.scan import khovanov_rank


MORTON = [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]


class BraidReductionTests(unittest.TestCase):
    def test_right_and_left_destabilizations_preserve_full_khovanov_rank(self):
        # No braid classifier is used as the oracle for these Markov moves.
        for original in ([1, 2], [1, -2] * 2, [1, 1, 1, 2]):
            expected = khovanov_rank(Diagram.from_braid(3, original).pd)["reduced_rank"]
            for sign in (-1, 1):
                for side in ("left", "right"):
                    if side == "right":
                        word = list(original) + [3 * sign]
                    else:
                        word = [g + 1 if g > 0 else g - 1 for g in original] + [sign]
                    strands, reduced, certificate = singleton_reduce(4, word)
                    self.assertEqual(strands, 3)
                    self.assertEqual(verify_singleton_reduction(4, word, certificate),
                                     (strands, reduced))
                    observed = khovanov_rank(Diagram.from_braid(4, word).pd)["reduced_rank"]
                    final = khovanov_rank(Diagram.from_braid(strands, reduced).pd)["reduced_rank"]
                    self.assertEqual(observed, expected)
                    self.assertEqual(final, expected)

    def test_conjugated_repeated_stabilization(self):
        rng = random.Random(260107)
        word = [1, -2]
        for strands in range(4, 12):
            word.append((strands - 1) * rng.choice((-1, 1)))
            conjugator = [rng.randrange(1, strands) * rng.choice((-1, 1)) for _ in range(20)]
            conjugated = conjugator + word + [-g for g in reversed(conjugator)]
            reduced_strands, reduced, certificate = singleton_reduce(strands, conjugated)
            self.assertEqual(reduced_strands, 3)
            self.assertEqual(reduced, (1, -2))
            self.assertEqual(len(certificate["steps"]), strands - 3)
            self.assertEqual(verify_singleton_reduction(strands, conjugated, certificate),
                             (3, (1, -2)))

    def test_morton_unknot_requires_a_more_general_operation(self):
        strands, word, certificate = singleton_reduce(4, MORTON)
        self.assertEqual(strands, 4)
        self.assertEqual(list(word), MORTON)
        self.assertEqual(certificate["steps"], [])
        self.assertEqual(khovanov_rank(Diagram.from_braid(4, MORTON).pd)["reduced_rank"], 1)

    def test_tampering_is_rejected(self):
        original = [1, -2, 3]
        for malformed in (None, [], "certificate"):
            with self.assertRaises(ValueError):
                verify_singleton_reduction(4, original, malformed)
        _, _, certificate = singleton_reduce(4, original)
        malformed = copy.deepcopy(certificate)
        malformed["steps"] = [None]
        with self.assertRaises(ValueError):
            verify_singleton_reduction(4, original, malformed)
        bad = copy.deepcopy(certificate)
        bad["steps"][0]["position"] = 0
        with self.assertRaises(ValueError):
            verify_singleton_reduction(4, original, bad)
        bad = copy.deepcopy(certificate)
        bad["final_word"] = [1, 1, 1, 2]
        with self.assertRaises(ValueError):
            verify_singleton_reduction(4, original, bad)
        # Same length and alleged local index cannot authorize a non-singleton deletion.
        with self.assertRaises(ValueError):
            verify_singleton_reduction(4, [3, -2, 3], certificate)


if __name__ == "__main__":
    unittest.main()
