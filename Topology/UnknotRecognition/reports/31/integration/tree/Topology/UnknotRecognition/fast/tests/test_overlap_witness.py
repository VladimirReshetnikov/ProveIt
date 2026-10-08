"""Independent literal audits of thresholded cyclic-overlap witnesses."""
from copy import deepcopy
import itertools
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, compressed_overlap, compressed_search
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_overlap import cyclic_overlap_move, apply_cyclic_overlap
from fastunknot.group_certificate import (
    _Budget, _certificate_version, _presentation, _reduce, verify_group_certificate,
)
from fastunknot.relator_overlap import apply_overlap
from test_compressed_lcs import parsed


def literal_cyclic_matches(left, right):
    """Enumerate signed cyclic factors directly, without grammar operations."""
    matches = []
    for inverse in (False, True):
        source = [-x for x in right[::-1]] if inverse else right
        for i in range(len(left)):
            for j in range(len(right)):
                length = 0
                while (length < min(len(left), len(right))
                       and left[(i+length) % len(left)] == source[(j+length) % len(source)]):
                    length += 1
                matches.append((length, i, j, inverse))
    return matches


def literal_reduce(word):
    stack = []
    for value in word:
        if stack and stack[-1] == -value:
            stack.pop()
        else:
            stack.append(value)
    while len(stack) > 1 and stack[0] == -stack[-1]:
        stack = stack[1:-1]
    return stack


class OverlapWitnessTests(unittest.TestCase):
    def test_existence_soundness_and_local_maximality_against_literal_oracle(self):
        rng = random.Random(3111)
        binary = [list(w) for n in range(1, 5) for w in itertools.product((1, 2), repeat=n)]
        pairs = list(itertools.product(binary, binary))
        pairs += [tuple(literal_reduce([rng.choice((-3, -2, -1, 1, 2, 3))
                                       for _ in range(rng.randrange(1, 21))])
                        for _ in range(2)) for _ in range(400)]
        for words in pairs:
            if not all(words):
                continue
            expected = max(x[0] for x in literal_cyclic_matches(*words))
            arena = WordArena(max_work=20000000)
            roots = [parsed(arena, word, rng) for word in words]
            move = cyclic_overlap_move(arena, roots, witness_first=True)
            self.assertEqual(move is not None, 2*expected > min(map(len, words)), words)
            if move is None:
                continue
            left, right = words[move['target']], words[move['donor']]
            if move['inverse']:
                right = [-x for x in right[::-1]]
            i, j, k = move['target_rotation'], move['donor_rotation'], move['overlap']
            lrot, rrot = left[i:]+left[:i], right[j:]+right[:j]
            self.assertEqual(lrot[:k], rrot[:k])
            self.assertGreater(2*k, len(right))
            if k < len(right):
                self.assertNotEqual(left[(i+k) % len(left)], right[(j+k) % len(right)])
                self.assertNotEqual(left[(i-1) % len(left)], right[(j-1) % len(right)])
            want = literal_reduce([-x for x in rrot[k:][::-1]]+lrot[k:])
            apply_cyclic_overlap(arena, roots, move)
            self.assertEqual(arena.expand(roots[move['target']]), want)
            self.assertLess(sum(arena.lengths[x] for x in roots), sum(map(len, words)))

    def test_equal_bigram_exponential_family_avoids_optimality_tables(self):
        tail = [1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3]
        for bits, interior in itertools.product((8, 32, 100, 500), (False, True)):
            arena, n = WordArena(max_work=100000), 2**bits
            run = arena.power(arena.from_word([1, 2]), n)
            tails = [arena.from_word([x]+tail+[y]) for x, y in ((3, 1), (1, 2))]
            roots = [arena.concat(t, run) if interior else arena.concat(run, t) for t in tails]
            before = sum(arena.lengths[x] for x in roots)
            with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
                 patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('witness suffices')):
                self.assertIsNone(compressed_overlap.whole_donor_move(arena, roots))
                move = cyclic_overlap_move(arena, roots, witness_first=True)
                self.assertEqual(move['overlap'], 2*n)
                apply_cyclic_overlap(arena, roots, move)
            self.assertEqual(before-sum(arena.lengths[x] for x in roots), 2*n-14)
            self.assertEqual(arena.stats.get('lcs_cut_pairs', 0), int(interior))
            self.assertEqual(arena.stats['overlap_witness_extensions'], 1)

    def test_greedy_gain_can_change_and_historical_default_is_retained(self):
        # Both alignments shorten. The first maximal one has length five;
        # another has length seven. There is no full donor spelling in target.
        donor = list(range(1, 9))
        target = list(range(1, 6))+[9, 10, 11]+list(range(1, 8))+[12]
        arena = WordArena()
        roots = [arena.from_word(donor), arena.from_word(target)]
        self.assertIsNone(compressed_overlap.whole_donor_move(arena, roots))
        old = cyclic_overlap_move(arena, roots)
        new = cyclic_overlap_move(arena, roots, witness_first=True)
        self.assertEqual(old['overlap'], 7)
        self.assertEqual(new['overlap'], 5)
        for bad in (0, 1, None, 'yes'):
            with self.assertRaises(ValueError):
                cyclic_overlap_move(arena, roots, witness_first=bad)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            cyclic_overlap_move(arena, roots, witness_first=True)
        arena = WordArena()
        roots = [arena.from_word(donor), arena.from_word(target)]
        arena.max_nodes = len(arena.rules)-1
        with self.assertRaises(CompressedLimit):
            cyclic_overlap_move(arena, roots, witness_first=True)

    def test_actual_gordian_trace_independent_replay_and_forgery_rejection(self):
        path = Path(__file__).parent/'fixtures/gordian_relator_power.json'
        record = json.loads(path.read_text())
        diagram, original = Diagram.from_pd(record['pd']), record['certificate']
        index = next(i for i, move in enumerate(original['moves']) if move['kind'] == 'relator_power')
        moves = deepcopy(original['moves'][:index])
        budget = _Budget(lambda: None, 200000, 20000000)
        alive, words = _presentation(diagram, budget)
        # Replay the existing prefix to a real reachable ten-generator state.
        for move in moves:
            if move['kind'] == 'relator':
                apply_overlap(words, move, budget, _reduce)
                continue
            self.assertEqual(move['kind'], 'eliminate')
            relation, g = move['relation'], move['generator']
            word = words[relation]
            pos = next(i for i, x in enumerate(word) if abs(x) == g)
            rest = word[pos+1:]+word[:pos]
            value = [-x for x in rest[::-1]] if word[pos] > 0 else rest
            inverse = [-x for x in value[::-1]]
            words[relation] = []
            alive.remove(g)
            words = [literal_reduce([y for x in w for y in
                     (value if x == g else inverse if x == -g else [x])]) for w in words]
        arena = WordArena(max_work=20000000)
        roots = [arena.reduce(arena.from_word(word)) for word in words]
        move = cyclic_overlap_move(arena, roots, witness_first=True)
        self.assertIsNotNone(move)
        self.assertGreater(arena.stats.get('overlap_witness_queries', 0), 0)
        apply_cyclic_overlap(arena, roots, move)
        moves.append(move)
        self.assertTrue(compressed_search._search(arena, roots, alive, moves, relator_moves=True))
        certificate = dict(original, moves=moves, version=_certificate_version(moves),
                           remaining_generator=next(iter(alive)))
        for compressed in (False, True):
            with patch.object(compressed_overlap, 'cyclic_overlap_move', side_effect=AssertionError), \
                 patch.object(compressed_overlap, '_extend_cyclic_witness', side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(diagram, certificate,
                    compressed=compressed, max_work=20000000))
            bad = deepcopy(certificate)
            bad['moves'][index]['overlap'] += 1
            self.assertFalse(verify_group_certificate(diagram, bad,
                compressed=compressed, max_work=20000000))


if __name__ == '__main__':
    unittest.main()
