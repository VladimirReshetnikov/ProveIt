"""Regression risks distinct from the exhaustive literal research audit."""

from copy import deepcopy
import unittest

from fastunknot.compressed_words import WordArena
from fastunknot.cyclic_basis import cyclic_basis_blocks, literal_cyclic_basis
from fastunknot.cyclic_basis_verify import verify_cyclic_basis, verify_literal_cyclic_basis
from fastunknot.signed_annulus_basis import compile_signed_quotient
from fastunknot.signed_annulus_basis_verify import _quotient_words


class CyclicBasisTests(unittest.TestCase):
    def test_unimodularity_and_separate_primitivity_are_insufficient(self):
        for words in ([[1, 1, 2, 2, 2], [1, 2, 2]],
                      [[1], [1, 2, 2]], [[1], [1]]):
            self.assertEqual(literal_cyclic_basis(words, [1, 2])['status'], 'INCONCLUSIVE')

    def test_independent_conjugators_and_small_blocks(self):
        words = [[2, 1, -2], [1, 2, -1], [3, 4], [3, 4, 4], [-7]]
        answer = literal_cyclic_basis(words, [1, 2, 3, 4, 5, 6, 7])
        self.assertEqual(answer['status'], 'COMPLETE')
        self.assertTrue(verify_literal_cyclic_basis(words, [1, 2, 3, 4, 5, 6, 7],
                                                   answer['certificate']))

    def test_general_checker_can_verify_beyond_producer_class(self):
        # a[b,c], b, c is a basis with identity homology, but support rank3.
        words = [[1, 2, 3, -2, -3], [2], [3]]
        answer = literal_cyclic_basis(words, [1, 2, 3])
        self.assertEqual(answer['reason'], 'unsupported_support_block')
        proof = dict(schema='cyclic-basis-nielsen-v1', generators=[1, 2, 3],
            targets=[1, 2, 3], moves=[
                dict(kind='multiply', target=1, donor=donor, exponent=exponent, side='right')
                for donor, exponent in ((2, -1), (3, -1), (2, 1), (3, 1))])
        self.assertTrue(verify_literal_cyclic_basis(words, [1, 2, 3], proof))

    def test_alphabet_validation_before_cyclic_reduction(self):
        for word in ([3], [3, 1, -3], [3, -3, 1]):
            with self.assertRaises(ValueError):
                literal_cyclic_basis([word], [1, 2])
        good = literal_cyclic_basis([[1], [2]], [1, 2])['certificate']
        for bad in ([True, 2], [1.0, 2.0]):
            proof = deepcopy(good)
            proof['generators'] = bad
            self.assertFalse(verify_literal_cyclic_basis([[1], [2]], [1, 2], proof))

    def test_exponential_passive_transport_stays_compressed(self):
        depth = 512
        chain = list(range(3, depth + 3)) + [2]
        packet = dict(method='column_leaf',
            active=[dict(two_handle=i, word=[chain[i], -chain[i+1], -chain[i+1]])
                    for i in range(depth)],
            passive=[dict(word=[1, chain[0]])],
            components=[dict(generators=[1, 2] + chain[:-1], surviving_generators=[1, 2])],
            cancellations=[[i, chain[i]] for i in range(depth)])
        a = WordArena(max_nodes=100000, max_work=1000000)
        roots = compile_signed_quotient(a, packet)
        self.assertEqual(a.lengths[roots[0]], (1 << depth) + 1)
        self.assertLess(len(a.rules), 3 * depth)
        result = cyclic_basis_blocks(a, roots, [1, 2])
        self.assertEqual(result['status'], 'COMPLETE')
        b = WordArena(max_nodes=100000, max_work=1000000)
        independent = _quotient_words(b, packet)
        self.assertTrue(verify_cyclic_basis(b, independent, [1, 2], result['certificate']))
        invalid = deepcopy(packet)
        invalid['active'][-1]['word'].append(chain[0])
        self.assertIsNone(_quotient_words(WordArena(), invalid))

    def test_budget_is_a_refusal(self):
        result = literal_cyclic_basis([[1, 2]], [1, 2], max_nodes=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'compressed_word_budget')


if __name__ == '__main__':
    unittest.main()
