"""Quotient deletion, exact uniform summaries and independent version-4 replay."""
from copy import deepcopy
import json
from math import gcd
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_overlap import whole_donor_move, apply_whole_donor
from fastunknot.compressed_search import _search
from fastunknot.compressed_group import verify_moves
from fastunknot.group_certificate import _Budget, _certificate_version, verify_group_certificate


class RelatorPowerTests(unittest.TestCase):
    def test_uniform_summaries_and_noncanonical_exponential_queries(self):
        rng, arena = random.Random(2706), WordArena()
        for _ in range(400):
            word = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 80))]
            if rng.randrange(3) == 0:
                word = [word[0]]*len(word)
            nodes = [arena.letter(x) for x in word]
            while len(nodes) > 1:
                i = rng.randrange(len(nodes)-1)
                nodes[i:i+2] = [arena.concat(nodes[i], nodes[i+1])]
            self.assertEqual(arena.uniform[nodes[0]], word[0] if len(set(word)) == 1 else 0)
            self.assertEqual(arena.uniform[arena.inverse(nodes[0])], -arena.uniform[nodes[0]])
        arena, n = WordArena(), 2**500
        power = arena.power(arena.letter(1), n)
        a, b = arena.concat(power, arena.letter(1)), arena.concat(arena.letter(1), power)
        self.assertNotEqual(a, b)
        before = len(arena.rules)
        with patch.object(arena, '_prefix_probe', side_effect=AssertionError('uniform query must be constant work')):
            self.assertTrue(arena.equal(a, b))
            for cap in (0, 1, n-1, n, n+1, n+2):
                self.assertEqual(arena.lcp(a, b, cap), min(n+1, cap))
        self.assertEqual(len(arena.rules), before)
        self.assertFalse(arena.equal(a, arena.inverse(b)))
        mixed = arena.concat(arena.concat(arena.slice(a, 0, n//2), arena.letter(2)),
                             arena.slice(a, n//2+1, n+1))
        self.assertEqual(arena.uniform[mixed], 0)
        self.assertFalse(arena.equal(a, mixed))
        self.assertEqual(arena.lcp(a, mixed), n//2)
        self.assertEqual(arena.reduce(arena.concat(a, arena.inverse(b))), 0)
        with self.assertRaises(ValueError):
            arena.lcp(a, b, True)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            arena.lcp(a, b)

    def test_maximal_copies_at_the_chosen_cyclic_occurrence(self):
        rng = random.Random(2707)
        for _ in range(300):
            arena = WordArena()
            donor = [rng.choice((1, 2, 3)) for _ in range(rng.randrange(1, 8))]
            copies = rng.randrange(2, 12)
            block = donor*copies+[4, 5]
            offset = rng.randrange(len(block))
            target = block[offset:]+block[:offset]
            if rng.randrange(2):
                donor = [-x for x in reversed(donor)]
            roots = [arena.from_word(donor), arena.from_word(target)]
            move = whole_donor_move(arena, roots)
            self.assertIsNotNone(move)
            pattern = [-x for x in reversed(donor)] if move['inverse'] else donor
            rotated = target[move['target_rotation']:]+target[:move['target_rotation']]
            expected = 0
            while rotated[expected*len(pattern):(expected+1)*len(pattern)] == pattern:
                expected += 1
            self.assertEqual(move.get('copies', 1), expected)
            self.assertGreaterEqual(expected, 1)
            apply_whole_donor(arena, roots, move)
            self.assertEqual(arena.expand(roots[1]), rotated[expected*len(pattern):])
        # A partial last copy is retained, including a cyclic seam.
        arena = WordArena()
        roots = [arena.from_word([1, 2]), arena.from_word([1, 2]*3+[1, 3])]
        move = whole_donor_move(arena, roots)
        self.assertEqual(move['copies'], 3)
        apply_whole_donor(arena, roots, move)
        self.assertEqual(arena.expand(roots[1]), [1, 3])

    def test_exponential_quotients_and_euclidean_descent(self):
        pairs = [(2**h, 2**(2*h)+1) for h in (8, 32, 100, 500)]
        x, y = 1, 1
        for _ in range(120):
            x, y = y, x+y
        pairs.extend(((x, y), (6*x, 6*y)))
        rng = random.Random(2708)
        pairs.extend((rng.randrange(2, 100), rng.randrange(2, 100)) for _ in range(100))
        for x, y in pairs:
            arena = WordArena(max_work=20000000)
            roots = [arena.power(arena.letter(1), x), arena.power(arena.letter(1), y)]
            moves = []
            with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
                success = _search(arena, roots, {1, 2}, moves, relator_moves=True, max_letters=0)
            self.assertEqual(success, gcd(x, y) == 1)
            self.assertLessEqual(len(moves), 2*max(x, y).bit_length()+1)
            if y == x*x+1:
                self.assertEqual(len(moves), 2)
                self.assertEqual(moves[0]['copies'], x)
                self.assertEqual(_certificate_version(moves), 4)

    def test_prune_ineligible_donor_before_building_its_inverse(self):
        arena = WordArena(max_nodes=600)
        donor = arena.power(arena.letter(1), 2**500)
        target = arena.concat(arena.letter(2), arena.concat(donor, arena.from_word([-2, 1])))
        roots = [donor, target]
        with patch.object(arena, 'inverse', side_effect=AssertionError('positive match needs no inverse')):
            move = whole_donor_move(arena, roots)
        self.assertEqual(move['kind'], 'relator')
        apply_whole_donor(arena, roots, move)
        self.assertEqual(arena.expand(roots[1]), [1])
        self.assertLess(len(arena.rules), 600)

    def test_genuine_gordian_trace_both_replayers_and_forged_macros(self):
        record = json.loads((Path(__file__).parent/'fixtures/gordian_relator_power.json').read_text())
        d, cert = Diagram.from_pd(record['pd']), record['certificate']
        index = next(i for i, move in enumerate(cert['moves']) if move['kind'] == 'relator_power')
        for compressed in (False, True):
            with patch('fastunknot.compressed_overlap.whole_donor_move', side_effect=AssertionError), \
                 patch('fastunknot.compressed_overlap.apply_whole_donor', side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d, cert, compressed=compressed, max_work=20000000))
            for field, value in (('copies', True), ('copies', 1), ('copies', -1), ('copies', 2.0),
                                 ('copies', 2**500), ('overlap', 3),
                                 ('target_rotation', cert['moves'][index]['target_rotation']+1),
                                 ('extra', 1)):
                bad = deepcopy(cert)
                bad['moves'][index][field] = value
                self.assertFalse(verify_group_certificate(d, bad, compressed=compressed, max_work=20000000), field)
            for version in (1, 2, 3, 5):
                bad = deepcopy(cert)
                bad['version'] = version
                self.assertFalse(verify_group_certificate(d, bad, compressed=compressed, max_work=20000000))

    def test_huge_quotient_compressed_replay_from_small_abstract_relators(self):
        # Internal move replay on a supplied presentation, not a knot verdict.
        n = 2**500
        cert = dict(version=4, remaining_generator=3, moves=[
            dict(kind='whitehead_power', multiplier=1, subset=[1, 2], exponent=n),
            dict(kind='relator_power', target=1, donor=0, target_rotation=1,
                 donor_rotation=0, inverse=False, overlap=1, copies=n+1),
            dict(kind='eliminate', relation=0, generator=1),
            dict(kind='eliminate', relation=1, generator=2)])
        stats = {}
        with patch.object(WordArena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertTrue(verify_moves([[1], [2, 1]], {1, 2, 3}, cert,
                _Budget(lambda: None, 20, 20000000), 100000, stats))
        self.assertGreater(stats['largest_word_bits'], 500)
        bad = deepcopy(cert)
        bad['moves'][1]['copies'] = n+3
        self.assertFalse(verify_moves([[1], [2, 1]], {1, 2, 3}, bad,
            _Budget(lambda: None, 20, 20000000), 100000, {}))
        with self.assertRaises(CompressedLimit):
            verify_moves([[1], [2, 1]], {1, 2, 3}, cert,
                _Budget(lambda: None, 20, 20000000), 20, {})


if __name__ == '__main__':
    unittest.main()
