"""Exact SLP equality, free reduction and compressed knot-certificate replay."""
import copy
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.group_certificate import group_certificate, verify_group_certificate, group_decide, GroupLimit
from fastunknot.scan import ScanLimit
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS

ROOT = Path(__file__).resolve().parents[1]


def explicit_reduce(word, cyclic=False):
    stack = []
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    if cyclic:
        while len(stack) > 1 and stack[0] == -stack[-1]:
            stack = stack[1:-1]
    return stack


def inflated_certificate(iterations):
    """Artificial verifier stress, not a difficult unknot-recognition input."""
    diagram = Diagram.from_pd(Diagram.from_braid(2, [1, -1, 1]).pd)
    certificate = group_certificate(diagram)
    forward = [dict(kind='whitehead', multiplier=a, subset=[1, 2])
               for _ in range(iterations) for a in (1, 2)]
    inverse = [dict(kind='whitehead', multiplier=-move['multiplier'],
                    subset=sorted((set(move['subset'])-{move['multiplier']})|{-move['multiplier']}))
               for move in reversed(forward)]
    certificate['moves'] = forward+inverse+certificate['moves']
    return diagram, certificate


class CompressedWordsTests(unittest.TestCase):
    def test_random_grammars_against_explicit_words(self):
        rng = random.Random(2685)
        for _ in range(400):
            arena, nodes, words = WordArena(), [0], [[]]
            for _ in range(30):
                if rng.randrange(3) == 0:
                    word = [rng.choice((-3, -2, -1, 1, 2, 3))]
                    node = arena.from_word(word)
                else:
                    a, b = rng.randrange(len(nodes)), rng.randrange(len(nodes))
                    node, word = arena.concat(nodes[a], nodes[b]), words[a]+words[b]
                nodes.append(node)
                words.append(word)
            for node, word in zip(nodes, words):
                self.assertTrue(arena.equal(node, arena.from_word(word)))
                self.assertEqual(arena.expand(arena.reduce(node)), explicit_reduce(word))
                self.assertEqual(arena.expand(arena.cyclic_reduce(node)), explicit_reduce(word, True))
                self.assertEqual(arena.expand(arena.inverse(node)), [-x for x in reversed(word)])
                lo = rng.randrange(len(word)+1)
                hi = rng.randrange(lo, len(word)+1)
                self.assertEqual(arena.expand(arena.slice(node, lo, hi)), word[lo:hi])
            for _ in range(8):
                i, j = rng.randrange(len(nodes)), rng.randrange(len(nodes))
                self.assertEqual(arena.equal(nodes[i], nodes[j]), words[i] == words[j])
                expected = 0
                while expected < min(len(words[i]), len(words[j])) and words[i][expected] == words[j][expected]:
                    expected += 1
                self.assertEqual(arena.lcp(nodes[i], nodes[j]), expected)
            if len(words[-1]) > 2:
                bad = words[-1].copy()
                bad[len(bad)//2] = 7  # Same endpoints and length; equality must inspect the interior.
                self.assertFalse(arena.equal(nodes[-1], arena.from_word(bad)))

    def test_compaction_and_noncanonical_exponential_words(self):
        # Noncanonical periodic parses exercise compaction on both equal and
        # unequal words, beyond structural-identity and endpoint shortcuts.
        rng = random.Random(2683)
        arena = WordArena()
        atom, nodes = arena.from_word([1, 2]), []
        nodes.append(atom)
        for _ in range(70):
            nodes.append(arena.concat(rng.choice(nodes), rng.choice(nodes)))
        left = arena.concat(nodes[-1], arena.letter(1))
        right = arena.concat(arena.letter(1), arena.power(arena.from_word([2, 1]),
                                                         arena.lengths[nodes[-1]]//2))
        self.assertTrue(arena.equal(left, right))
        self.assertGreater(arena.stats['compact_triples'], 0)
        before = arena.stats['compact_triples']
        k = arena.lengths[right]//2
        bad = arena.concat(arena.concat(arena.slice(right, 0, k), arena.letter(3)),
                           arena.slice(right, k+1, arena.lengths[right]))
        self.assertFalse(arena.equal(left, bad))
        self.assertGreater(arena.stats['compact_triples'], before)
        arena = WordArena()
        power = 2**100
        left = arena.concat(arena.power(arena.from_word([1, 2]), power), arena.letter(1))
        right = arena.concat(arena.letter(1), arena.power(arena.from_word([2, 1]), power))
        with patch.object(arena, 'expand', side_effect=AssertionError('must stay compressed')):
            self.assertTrue(arena.equal(left, right))
            self.assertEqual(arena.reduce(arena.concat(left, arena.inverse(right))), 0)
            middle = arena.lengths[left]//2
            bad = arena.concat(arena.concat(arena.slice(left, 0, middle), arena.letter(3)),
                               arena.slice(left, middle+1, arena.lengths[left]))
            self.assertFalse(arena.equal(left, bad))
        self.assertLess(len(arena.rules), 20000)

    def test_compressed_substitution_cyclic_reduction_and_deep_grammars(self):
        arena = WordArena()
        count = 2**80
        root = arena.power(arena.from_word([1, -2, 3]), count)
        image = arena.substitute([root], {1: arena.from_word([1, 2])})[0]
        self.assertTrue(arena.equal(image, arena.power(arena.from_word([1, 3]), count)))
        self.assertEqual(arena.occurrence(image, 1), (count, 0, 1))
        self.assertEqual(arena.occurrence(image, 2), (0, None, None))
        tail = arena.concat(arena.power(arena.letter(1), count), arena.letter(-3))
        self.assertEqual(arena.occurrence(tail, 3), (1, count, -3))
        conjugate = arena.concat(arena.concat(image, arena.letter(4)), arena.inverse(image))
        self.assertEqual(arena.expand(arena.cyclic_reduce(conjugate)), [4])
        deep = arena.power(arena.letter(5), 2**1500)
        center = arena.lengths[deep]//2
        self.assertEqual(arena.expand(arena.slice(deep, center+3, center+5)), [5, 5])
        self.assertEqual(arena.lengths[arena.inverse(deep)], 2**1500)

    def test_real_certificates_and_forged_evidence(self):
        for _, strands, word in SURVIVORS:
            d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
            c = group_certificate(d)
            with patch('fastunknot.compressed_words.WordArena.expand', side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d, c, compressed=True))
        for i in (3, 8):
            _, strands, word = SURVIVORS[i]
            d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
            d = d.mirror()
            c = group_certificate(d, relator_moves=True)
            self.assertTrue(verify_group_certificate(d, c, compressed=True))
            index = next(i for i, m in enumerate(c['moves']) if m['kind'] == 'relator')
            bad = copy.deepcopy(c)
            bad['moves'][index]['donor'] = bad['moves'][index]['target']
            self.assertFalse(verify_group_certificate(d, bad, compressed=True))
        d = Diagram.from_json(json.loads((ROOT/'normal_research/gordian.json').read_text()))
        c = group_certificate(d, relator_moves=True, max_work=10000000)
        self.assertTrue(verify_group_certificate(d, c, compressed=True, max_work=10000000))
        for key, value in [('remaining_generator', 0), ('version', True), ('input_pd', [])]:
            bad = copy.deepcopy(c)
            bad[key] = value
            self.assertFalse(verify_group_certificate(d, bad, compressed=True, max_work=10000000))

    def test_exponential_trace_without_expanded_words(self):
        diagram, certificate = inflated_certificate(64)
        with self.assertRaises(GroupLimit):
            verify_group_certificate(diagram, certificate)
        stats = {}
        self.assertTrue(verify_group_certificate(diagram, certificate, compressed=True, stats=stats))
        self.assertGreaterEqual(stats['largest_word_bits'], 89)
        self.assertLess(stats['nodes'], 1000)
        bad = copy.deepcopy(certificate)
        bad['moves'][0]['subset'].append(-bad['moves'][0]['multiplier'])
        self.assertFalse(verify_group_certificate(diagram, bad, compressed=True))

    def test_budgets_global_cancellation_and_cli(self):
        with self.assertRaises(CompressedLimit):
            WordArena(max_nodes=0).letter(1)
        with self.assertRaises(CompressedLimit):
            WordArena(max_work=0).letter(1)
        def cancel():
            raise ScanLimit('global compressed cancellation')
        with self.assertRaises(ScanLimit):
            WordArena(check=cancel).letter(1)
        diagram, c = inflated_certificate(16)
        for options in ({'max_nodes': 0}, {'max_work': 0}):
            with self.assertRaises(GroupLimit):
                verify_group_certificate(diagram, c, compressed=True, **options)
        with self.assertRaises(ScanLimit):
            verify_group_certificate(diagram, c, compressed=True, check=cancel)
        with self.assertRaises(ValueError):
            group_decide(diagram, compressed_verification=1)
        for options in ({'compressed': 1}, {'max_nodes': -1}, {'stats': []}):
            with self.assertRaises(ValueError):
                verify_group_certificate(diagram, c, **options)
        _, strands, word = SURVIVORS[0]
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        result = recognize(Diagram.from_pd(d.pd), use_group=True, group_compressed=True, group_seconds=None)
        self.assertEqual(result.evidence['group']['verification_backend'], 'compressed-slp')
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-',
                              '--group-compressed', '--group-seconds', '2'],
                             input=json.dumps({'pd': d.pd}), text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['evidence']['group']['verification_backend'], 'compressed-slp')


if __name__ == '__main__':
    unittest.main()
