"""Exact compressed occurrence tables and whole-donor normal-closure moves."""
from copy import deepcopy
from itertools import product
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_match import MatchTable, first_occurrence, _intersect
from fastunknot.compressed_overlap import whole_donor_move, apply_whole_donor
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import _presentation, _Budget, verify_group_certificate
from fastunknot.whitehead_power import powered_images
from fastunknot.scan import ScanLimit


def expand_ap(ap):
    return [] if ap is None else [ap[0]+i*ap[1] for i in range(ap[2])]


class CompressedMatchTests(unittest.TestCase):
    def test_exhaustive_binary_pattern_matching(self):
        count = 0
        for n in range(1, 8):
            for text in product((1, 2), repeat=n):
                for m in range(1, min(n, 4)+1):
                    for pattern in product((1, 2), repeat=m):
                        arena = WordArena()
                        p, t = arena.from_word(pattern), arena.from_word(text)
                        expected = next((i for i in range(n-m+1) if text[i:i+m] == pattern), None)
                        self.assertEqual(MatchTable(arena, p, t).first(), expected)
                        self.assertEqual(first_occurrence(arena, p, t), expected)
                        count += 1
        self.assertEqual(count, 7340)

    def test_random_parses_all_cells_and_local_intervals(self):
        rng = random.Random(2702)
        for _ in range(300):
            arena = WordArena()
            def parse(word):
                nodes = [arena.letter(x) for x in word]
                while len(nodes) > 1:
                    i = rng.randrange(len(nodes)-1)
                    nodes[i:i+2] = [arena.concat(nodes[i], nodes[i+1])]
                return nodes[0] if nodes else 0
            text = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 45))]
            if rng.randrange(2):
                lo, hi = sorted(rng.randrange(len(text)+1) for _ in range(2))
                pattern = text[lo:hi]
            else:
                pattern = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 20))]
            p, t = parse(pattern), parse(text)
            table = MatchTable(arena, p, t)
            literals = {node: arena.expand(node) for node in set(table.pattern_nodes+table.text_nodes)}
            for (pn, tn), ap in table.cells.items():
                a, b, rule = literals[pn], literals[tn], arena.rules[tn]
                cut = 0 if rule[0] == 't' else arena.lengths[rule[1]]
                expected = [i for i in range(max(0, cut-len(a)), min(cut, len(b)-len(a))+1)
                            if b[i:i+len(a)] == a]
                self.assertEqual(expand_ap(ap), expected)
            expected = next((i for i in range(len(text)-len(pattern)+1)
                             if text[i:i+len(pattern)] == pattern), None)
            self.assertEqual(table.first(), expected)
            self.assertEqual(first_occurrence(arena, p, t), expected)
            for _ in range(8):
                if not p:
                    break
                pn = rng.choice(table.pattern_nodes)
                size = arena.lengths[pn]
                alpha = rng.randrange(-size, len(text)+1)
                beta = alpha+rng.randrange(3*size+1)
                expected = [i for i in range(max(0, alpha), min(beta, len(text))-size+1)
                            if text[i:i+size] == literals[pn]]
                got = table.local(pn, t, alpha, beta)
                self.assertLessEqual(len(got), 2)
                self.assertEqual([i for ap in got for i in expand_ap(ap)], expected)

    def test_progression_intersections_without_enumeration(self):
        rng = random.Random(2703)
        for _ in range(3000):
            def ap():
                count = rng.randrange(1, 30)
                return rng.randrange(-20, 40), rng.randrange(1, 12) if count > 1 else 0, count
            a, b = ap(), ap()
            self.assertEqual(expand_ap(_intersect(a, b)), sorted(set(expand_ap(a)) & set(expand_ap(b))))
        n = 2**500
        self.assertEqual(_intersect((0, 6, n), (3, 9, n)), (12, 18, (6*(n-1)-12)//18+1))

    def test_huge_occurrence_progression_and_failed_first_candidate(self):
        arena, n = WordArena(), 2**60
        p = arena.power(arena.letter(1), n)
        text = arena.concat(p, p)
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            table = MatchTable(arena, p, text)
            self.assertEqual(table.cells[p, text], (0, 1, n+1))
            self.assertEqual(table.first(), 0)
        # The first literal candidate fails; the complete table must still
        # find a later match, beyond an exponentially long intervening block.
        arena, n = WordArena(), 2**32
        p = arena.power(arena.letter(1), n)
        text = arena.concat(arena.from_word([1, 2]), arena.concat(
            arena.power(arena.letter(2), n), p))
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertEqual(first_occurrence(arena, p, text), n+2)
        self.assertGreater(arena.stats['match_cells'], 0)
        self.assertEqual(first_occurrence(arena, 0, 0), 0)
        self.assertIsNone(first_occurrence(arena, p, 0))

    def test_budgets_global_cancellation_and_deep_grammar(self):
        arena = WordArena(max_nodes=20)
        p = arena.from_word([1, 2]*8)
        text = arena.from_word([2, 1]*32)
        with self.assertRaisesRegex(CompressedLimit, 'table allowance'):
            MatchTable(arena, p, text)
        arena = WordArena()
        p, t = arena.from_word([1, 2]), arena.from_word([2, 1, 2])
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            first_occurrence(arena, p, t)
        arena = WordArena()
        p, t = arena.from_word([1, 2]*8), arena.from_word([2, 1]*32)
        def cancel():
            if arena.stats.get('match_cells', 0) >= 10:
                raise ScanLimit('cancel compressed matching')
        arena.check = cancel
        with self.assertRaises(ScanLimit):
            MatchTable(arena, p, t)
        arena, t = WordArena(max_work=30000000), 0
        for _ in range(1500):
            t = arena.concat(t, arena.letter(1))
        self.assertEqual(MatchTable(arena, arena.from_word([1, 1]), t).first(), 0)

    def test_exponential_stalled_presentations_and_no_false_success(self):
        for bits in (10, 100, 500):
            arena = WordArena()
            donor = arena.power(arena.letter(1), 2**bits)
            target = arena.concat(arena.letter(2), arena.concat(donor, arena.from_word([-2, 1])))
            roots, moves = [donor, target], []
            with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
                self.assertTrue(_search(arena, roots, {1, 2}, moves, relator_moves=True, max_letters=4))
            self.assertEqual([m['kind'] for m in moves], ['relator', 'eliminate'])
            self.assertEqual(moves[0]['target_rotation'], 1)
            self.assertEqual(moves[0]['overlap'], 2**bits)
        arena = WordArena()
        roots = [arena.power(arena.letter(1), 2**100), arena.power(arena.letter(2), 2**100)]
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertFalse(_search(arena, roots, {1, 2}, [], relator_moves=True, max_letters=4))
        self.assertEqual(arena.stats.get('match_cells', 0), 0)

    def test_whole_donor_search_against_literal_cyclic_scan(self):
        rng = random.Random(2704)
        for _ in range(350):
            arena = WordArena()
            words = [[rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(rng.randrange(1, 16))]
                     for _ in range(rng.randrange(1, 6))]
            roots = [arena.from_word(w) for w in words]
            move = whole_donor_move(arena, roots)
            expected = []
            for donor, word in enumerate(words):
                for target, other in enumerate(words):
                    if target != donor and len(other) >= len(word):
                        for inverse in (False, True):
                            pattern = [-x for x in reversed(word)] if inverse else word
                            for start in range(len(other)):
                                if (other+other)[start:start+len(word)] == pattern:
                                    expected.append((len(word), donor, target, inverse, start))
            self.assertEqual(move is not None, bool(expected))
            if move:
                self.assertEqual(move['overlap'], max(x[0] for x in expected))
                target, donor = move['target'], move['donor']
                old_donor = roots[donor]
                apply_whole_donor(arena, roots, move)
                self.assertEqual(roots[donor], old_donor)
                self.assertLessEqual(arena.lengths[roots[target]], len(words[target])-len(words[donor]))

    def test_real_knot_trace_independent_replay_and_forgery(self):
        d = Diagram.from_pd(Diagram.from_braid(2, [1, -1, 1]).pd)
        for exponent in (7, 2**100):
            alive, words = _presentation(d, _Budget(lambda: None, 10000, 100000))
            arena = WordArena()
            roots = [arena.from_word(w) for w in words]
            roots = [arena.cyclic_reduce(x) for x in arena.substitute(
                roots, powered_images(arena, alive, 2, {1, 2}, exponent))]
            move = whole_donor_move(arena, roots)
            self.assertIsNotNone(move)
            apply_whole_donor(arena, roots, move)
            moves = [dict(kind='whitehead_power', multiplier=2, subset=[1, 2], exponent=exponent), move]
            self.assertTrue(_search(arena, roots, alive, moves, relator_moves=True))
            cert = dict(version=3, method='wirtinger-cyclic-group', status='UNKNOT',
                        input_pd=[list(r) for r in d.pd], moves=moves, remaining_generator=next(iter(alive)))
            for compressed in ((False, True) if exponent == 7 else (True,)):
                with patch('fastunknot.compressed_overlap.first_occurrence', side_effect=AssertionError):
                    self.assertTrue(verify_group_certificate(d, cert, compressed=compressed))
                bad = deepcopy(cert)
                bad['moves'][1]['donor'] = bad['moves'][1]['target']
                self.assertFalse(verify_group_certificate(d, bad, compressed=compressed))


if __name__ == '__main__':
    unittest.main()
