"""Independent literal-oracle and structural checks for the research circuit."""
import random
import unittest

from persistent_elimination import CircuitLimit, SignedCircuit, doubling_context_family


def inverse(word):
    return [-x for x in reversed(word)]


def literal_step(words, slot, generator):
    donor = words[slot]
    positions = [i for i, x in enumerate(donor) if abs(x) == generator]
    if len(positions) != 1:
        raise ValueError('not a singleton')
    p = positions[0]
    # Direct algebraic formula, independent of the circuit's sibling rotation.
    image = (inverse(donor[:p])+inverse(donor[p+1:])
             if donor[p] > 0 else donor[p+1:]+donor[:p])
    neg = inverse(image)
    result = []
    for index, word in enumerate(words):
        if index == slot:
            result.append([])
            continue
        out = []
        for x in word:
            out.extend(image if x == generator else neg if x == -generator else [x])
        result.append(out)
    return result, image


class PersistentEliminationTests(unittest.TestCase):
    def check_case(self, words, moves):
        arena = SignedCircuit()
        roots = [arena.from_word(word) for word in words]
        literal = [list(word) for word in words]
        d0 = max(arena.depths)
        for i, (slot, g) in enumerate(moves):
            before = arena.measurements(roots)
            literal, expected_image = literal_step(literal, slot, g)
            image = arena.eliminate(roots, slot, g)
            self.assertEqual(arena.expand(image), expected_image)
            self.assertEqual([arena.expand(root) for root in roots], literal)
            after = arena.measurements(roots)
            q = after['context_siblings']-before['context_siblings']
            self.assertLessEqual(q, (i+1)*(before['binding_free_height']+1))
            new_depth = 0 if q <= 1 else (q-1).bit_length()
            self.assertLessEqual(after['binding_free_height'],
                                 before['binding_free_height']+new_depth)
            self.assertLessEqual(after['full_height'],
                                 (i+2)*(after['binding_free_height']+1)-1)
            # Integer safe overestimate of D_i <= D0+6 i log2(D0+i+2).
            self.assertLessEqual(after['binding_free_height'],
                                 d0+6*(i+1)*(d0+i+3).bit_length())
        exported = arena.export_slp(roots)
        self.assertLessEqual(len(exported['rules'])-1, 2*(len(arena.rules)-1))
        expanded = [[]]
        for node, rule in enumerate(exported['rules'][1:], 1):
            if rule[0] == 't':
                expanded.append([rule[1]])
            else:
                self.assertTrue(0 < rule[1] < node and 0 < rule[2] < node)
                expanded.append(expanded[rule[1]]+expanded[rule[2]])
        self.assertEqual([expanded[root] for root in exported['roots']], literal)

    def test_empty_images_and_inverse_handles(self):
        self.check_case([[1], [2, -1, 3, 1], [-3, -2]], [(0, 1), (1, 2)])
        self.check_case([[-1], [1, -2, -1, 3]], [(0, 1), (1, 2)])

    def test_repeated_children_rejected(self):
        a = SignedCircuit()
        node = a.from_word([1, 2])
        root = a.concat(node, node)
        roots = [root]
        with self.assertRaises(ValueError):
            a.eliminate(roots, 0, 1)
        self.assertEqual(a.bindings, {})
        self.assertEqual(a.expand(root), [1, 2, 1, 2])

    def test_forward_bindings_and_exponential_raw_context(self):
        for k in range(1, 13):
            words, moves = doubling_context_family(k)
            self.check_case(words, moves)
            a = SignedCircuit()
            roots = [a.from_word(word) for word in words]
            for slot, g in moves:
                a.eliminate(roots, slot, g)
            self.assertEqual(a.measurements(roots)['root_lengths'][-1], (1 << k)+2)

    def test_600_random_presentation_traces(self):
        rng = random.Random(20261009)
        checked_moves = 0
        for _ in range(600):
            rank = rng.randrange(2, 8)
            words = [[rng.choice((-1, 1))*rng.randrange(1, rank+1)
                      for _ in range(rng.randrange(0, 11))]
                     for _ in range(rng.randrange(2, 10))]
            live = set(range(1, rank+1))
            literal, moves = [list(w) for w in words], []
            while live:
                candidates = [(slot, g) for slot, word in enumerate(literal)
                              for g in live if sum(abs(x) == g for x in word) == 1]
                if not candidates:
                    break
                slot, g = rng.choice(candidates)
                updated, _ = literal_step(literal, slot, g)
                if sum(map(len, updated)) > 20_000:
                    break
                literal = updated
                moves.append((slot, g))
                live.remove(g)
            self.check_case(words, moves)
            checked_moves += len(moves)
        self.assertGreater(checked_moves, 1000)

    def test_no_expansion_in_elimination(self):
        words, moves = doubling_context_family(128)
        arena = SignedCircuit(max_work=100_000_000)
        roots = [arena.from_word(word) for word in words]
        arena.expand = lambda *args, **kwargs: (_ for _ in ()).throw(
            AssertionError('expanded-word oracle called'))
        for slot, g in moves:
            arena.eliminate(roots, slot, g)
        info = arena.measurements(roots)
        self.assertEqual(info['root_lengths'][-1], (1 << 128)+2)
        self.assertLess(info['nodes'], 100_000)
        exported = arena.export_slp(roots)
        lengths = [0]
        for rule in exported['rules'][1:]:
            lengths.append(1 if rule[0] == 't' else lengths[rule[1]]+lengths[rule[2]])
        self.assertEqual(lengths[exported['roots'][-1]], (1 << 128)+2)
        self.assertLessEqual(len(exported['rules'])-1, 2*info['nodes'])

    def test_interruption_does_not_publish_binding(self):
        arena = SignedCircuit()
        roots = [arena.from_word([1, 2, 3]), arena.from_word([1, -3])]
        arena.max_work = arena.work+1
        with self.assertRaises(CircuitLimit):
            arena.eliminate(roots, 0, 1)
        self.assertEqual(arena.bindings, {})
        arena.max_work = 1_000_000
        arena.eliminate(roots, 0, 1)
        self.assertEqual(arena.expand(roots[1]), [-3, -2, -3])


if __name__ == '__main__':
    unittest.main()
