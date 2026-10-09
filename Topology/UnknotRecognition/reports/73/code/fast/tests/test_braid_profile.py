import copy
import itertools
import random
import unittest

from fastunknot.braid_profile import (
    _pack, structural_runs_certificate, structural_word_certificate,
    verify_structural_runs_certificate, signature_certificate,
    verify_signature_certificate,
)
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.recognize import recognize
from fastunknot.seifert import seifert_data, seifert_certificate


class BraidProfileTests(unittest.TestCase):
    def test_exhaustive_against_independent_pd_graph(self):
        checked = 0
        keys = ('crossings', 'writhe', 'seifert_circles', 'positive_components',
                'negative_components', 'homogeneity_defect', 'canonical_genus',
                'rasmussen_interval')
        for strands, max_length in ((2, 7), (3, 6)):
            alphabet = tuple(range(1, strands)) + tuple(range(-1, -strands, -1))
            for length in range(max_length + 1):
                for word in itertools.product(alphabet, repeat=length):
                    try:
                        diagram = Diagram.from_braid(strands, word)
                    except DiagramError:
                        continue
                    answer = structural_word_certificate(strands, word)
                    data = seifert_data(diagram)
                    self.assertEqual({k: answer[k] for k in keys}, data)
                    certificate = seifert_certificate(diagram)
                    expected = 'INCONCLUSIVE' if certificate is None else certificate['status']
                    self.assertEqual(answer['status'], expected)
                    checked += 1
        self.assertEqual(checked, 3026)

    def test_random_higher_braids_and_pipeline(self):
        rng = random.Random(835701)
        tested = 0
        while tested < 240:
            b = rng.randrange(4, 7)
            n = rng.randrange(b - 1, 17)
            word = [rng.choice((-1, 1)) * rng.randrange(1, b) for _ in range(n)]
            try:
                diagram = Diagram.from_braid(b, word)
            except DiagramError:
                continue
            direct = structural_word_certificate(b, word)
            graph = seifert_certificate(diagram)
            self.assertEqual(direct['status'], 'INCONCLUSIVE' if graph is None else graph['status'])
            old = recognize(diagram)
            new = recognize(diagram, use_braid_profile=True)
            self.assertEqual(old.status, new.status)
            tested += 1

    def test_binary_exponents_without_expansion(self):
        m = (1 << 100000) + 1
        runs = [(1, m), (2, -(2 * m - 1)), (3, m)]
        answer = structural_runs_certificate(4, runs)
        self.assertEqual(answer['status'], 'KNOTTED')
        self.assertEqual(answer['homogeneity_defect'], 0)
        self.assertEqual(answer['artin_exponent_sum'], 1)
        self.assertTrue(verify_structural_runs_certificate(4, runs, answer))

    def test_invalid_original_permutation_and_malformed_inputs(self):
        for b, runs in ((2, [(1, 2)]), (10**100, [(1, 1)]),
                        (3, [(1, 1)]), (2, [(1, 0)]), (2, [(True, 1)]),
                        (2, [(1, 1.0)]), (0, [])):
            with self.assertRaises(ValueError):
                structural_runs_certificate(b, runs)

    def test_signature_domination(self):
        rng = random.Random(112358)
        tested = 0
        while tested < 500:
            b = rng.randrange(2, 8)
            word = [rng.choice((-1, 1)) * rng.randrange(1, b)
                    for _ in range(rng.randrange(b - 1, 25))]
            try:
                structural = structural_word_certificate(b, word)
            except ValueError:
                continue
            signature = signature_certificate(b, word)
            low, high = structural['rasmussen_interval']
            self.assertLessEqual(signature['signature_abs_lower_bound'], max(0, low, -high))
            if signature['status'] == 'KNOTTED':
                self.assertEqual(structural['status'], 'KNOTTED')
                self.assertTrue(verify_signature_certificate(b, word, signature))
                forged = copy.deepcopy(signature)
                forged['definite_subspace_dimension'] += 1
                self.assertFalse(verify_signature_certificate(b, word, forged))
            tested += 1

    def test_path_optimizer_against_all_subsets(self):
        for size in range(7):
            for weights in itertools.product(range(3), repeat=size):
                exact = max(sum(weights[i] for i in range(size) if mask >> i & 1)
                            for mask in range(1 << size) if not mask & (mask << 1))
                result, indices = _pack(weights)
                self.assertEqual(result, exact)
                self.assertEqual(result, sum(weights[i - 1] for i in indices))
                self.assertTrue(all(y - x >= 2 for x, y in zip(indices, indices[1:])))

    def test_profile_replay_and_inconclusive(self):
        self.assertEqual(structural_runs_certificate(1, [])['status'], 'UNKNOT')
        runs = [(1, 1), (2, -1), (1, -1), (2, 1)]
        answer = structural_runs_certificate(3, runs)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        answer['canonical_genus'] += 1
        self.assertFalse(verify_structural_runs_certificate(3, runs, answer))

    def test_checked_source_option(self):
        source = Diagram.from_braid(4, [1]*3 + [-2]*5 + [3]*3)
        answer = recognize(source, use_braid_profile=True)
        self.assertEqual(answer.status, 'KNOTTED')
        self.assertIn('source_braid_structural', answer.evidence)
        pd_only = Diagram.from_pd(source.pd)
        self.assertNotIn('source_braid_structural', recognize(pd_only, use_braid_profile=True).evidence)


if __name__ == '__main__':
    unittest.main()
