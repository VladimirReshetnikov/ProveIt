import copy
import unittest

from fastunknot.free_group_elimination import certify_free_group, cyclic_reduce
from fastunknot.free_group_elimination_verify import replay_free_group


def rows(*words):
    return [dict(id=i, word=list(w)) for i, w in enumerate(words)]


class FreeGroupEliminationTests(unittest.TestCase):
    def assert_free(self, generators, relators, rank):
        result = certify_free_group(generators, relators)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['free_rank'], rank)
        replay = replay_free_group(generators, relators, result['certificate'])
        self.assertIsNotNone(replay)
        self.assertEqual(replay['free_rank'], rank)
        self.assertTrue(all(a >= b for a, b in zip(result['accepted_lengths'],
                                                 result['accepted_lengths'][1:])))
        return result

    def test_signed_substitution_crosses_stopping_set(self):
        result = self.assert_free([1, 2], rows([1, 2], [1, 2, 2]), 0)
        self.assertEqual(result['accepted_lengths'], [5, 1, 0])
        self.assertEqual(result['stats']['substitution_pivots'], 1)

    def test_negative_pivot_and_cyclic_conjugation(self):
        self.assert_free([1, 2, 3], rows([3, -1, 2, -3], [1, -2, 3]), 1)

    def test_trivial_relators_are_counted(self):
        result = self.assert_free([1, 2], rows([1, -1], [], [1]), 1)
        self.assertEqual(result['certificate']['trivial_relators'], [0, 1])

    def test_relationless_group_keeps_unused_generators(self):
        self.assert_free([1, 7, 40], [], 3)

    def test_fibonacci_automorphism_is_an_honest_refusal(self):
        # Images of a free basis under phi(a)=ab, phi(b)=a, iterated four times.
        relators = rows([1, 2, 1, 1, 2, 1, 2, 1], [1, 2, 1, 1, 2])
        result = certify_free_group([1, 2], relators)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['candidate_trials'], 0)

    def test_torsion_group_not_certified(self):
        self.assertEqual(certify_free_group([1], rows([1, 1]))['status'], 'INCONCLUSIVE')

    def test_certificate_mutations(self):
        generators, relators = [1, 2], rows([1, 2], [1, 2, 2])
        proof = self.assert_free(generators, relators, 0)['certificate']
        for field, value in [('free_rank', 1), ('free_rank', False),
                             ('free_generators', [1]), ('trivial_relators', [0]),
                             ('initial_reduced_length', 6), ('presentation_sha256', '0' * 64),
                             ('moves', []), ('moves', [[0, 99]]), ('policy', 'arbitrary')]:
            broken = copy.deepcopy(proof)
            broken[field] = value
            self.assertIsNone(replay_free_group(generators, relators, broken), field)

    def test_source_relator_bound_to_hash(self):
        source = rows([1, 2], [1, 2, 2])
        proof = self.assert_free([1, 2], source, 0)['certificate']
        altered = rows([1, -2], [1, 2, 2])
        self.assertIsNone(replay_free_group([1, 2], altered, proof))

    def test_cyclic_normalization_preserves_relative_signs(self):
        self.assertEqual(cyclic_reduce([3, 1, 2, -1, -3]), (2,))
        self.assertEqual(cyclic_reduce([3, 1, 2, -1, 2, -3]), (1, 2, -1, 2))
        self.assertEqual(cyclic_reduce([3, 1, -1, 2, -3]), (2,))
        self.assertEqual(cyclic_reduce([1, -1]), ())

    def test_invalid_labels(self):
        for generators, relators in [([True], []), ([0], []), ([1, 1], []),
                                      ([1], rows([2])), ([1], rows([0]))]:
            with self.assertRaises(ValueError):
                certify_free_group(generators, relators)

    def test_cooperative_stop(self):
        class Stop(RuntimeError):
            pass
        def check():
            raise Stop()
        with self.assertRaises(Stop):
            certify_free_group([1], rows([1]), check=check)
        with self.assertRaises(Stop):
            replay_free_group([1], rows([1]), {}, check=check)


if __name__ == '__main__':
    unittest.main()
