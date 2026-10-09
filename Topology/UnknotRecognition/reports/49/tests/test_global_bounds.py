"""Supplementary exact checks for the phase-independent analysis."""
from math import gcd
import random
import unittest
from anchored_unknot import Arena, Source, AnchoredState, replay
from anchored_unknot.fixtures import signed_tree, power_chain
from anchored_unknot.reference_update import apply_projection, native_witnesses


class TracedArena(Arena):
    def __init__(self):
        super().__init__()
        self.image_node_charge = 0

    def power(self, root, exponent):
        out = super().power(root, exponent)
        self.image_node_charge += len(self._reachable([out]))
        return out


class GlobalBoundsTests(unittest.TestCase):
    def test_reachable_not_allocated_recurrence(self):
        rng = random.Random(2026100803)
        for _ in range(60):
            r = rng.randrange(2, 15)
            s = signed_tree([rng.randrange(1, i) for i in range(2, r + 1)],
                            [rng.choice((-7, -3, 1, 2, 5)) for _ in range(r - 1)],
                            duplicates=True)
            st = AnchoredState(s)
            arena = TracedArena()
            _, roots = s.materialize(st.images, set(), arena)
            alive = set(s.generators)
            while len(alive) > 1:
                ws = st.plan(max_pairs=rng.choice((1, 2, 5)))
                old_s = len(arena._reachable(roots))
                old_a = len(arena.rules)
                arena.image_node_charge = 0
                apply_projection(arena, roots, alive, native_witnesses(ws))
                self.assertLessEqual(len(arena._reachable(roots)), old_s + arena.image_node_charge)
                self.assertLessEqual(len(arena.rules) - old_a, old_s + arena.image_node_charge)
                st.apply_planned(ws)

    def test_nonzero_character_sharpens_each_block(self):
        s = power_chain(12, 7)
        st = AnchoredState(s)
        h = {g: 7 ** (g - 1) for g in s.generators}
        while len(st.alive) > 1:
            st.apply_planned(st.plan(max_pairs=1))
            for target in st.alive:
                block = [g for g, (z, k) in st.images.items() if z == target]
                divisor = 0
                for g in block:
                    divisor = gcd(divisor, abs(h[g]))
                signs = {st.images[g][1] * divisor // h[g] for g in block}
                self.assertIn(signs, ({1}, {-1}))
                for g in block:
                    self.assertEqual(abs(st.images[g][1]), abs(h[g]) // divisor)

    def test_meridional_character_forces_unit_images(self):
        s = power_chain(40, 1)
        st = AnchoredState(s)
        while len(st.alive) > 1:
            st.apply_planned(st.plan(max_pairs=1))
            self.assertTrue(all(abs(k) == 1 for z, k in st.images.values()))
        self.assertTrue(replay(s, st.run()).rank_one_zero)

    def test_unused_long_source_rules_are_not_relators(self):
        # The determinant bound uses source relators; processing arbitrary unused
        # input gates must additionally charge their input-size/length metadata.
        a = Arena(); donor = a.word((1, -2))
        a.power(a.letter(2), 1 << 200)
        s = Source((1, 2), tuple(a.rules), (donor,))
        st = AnchoredState(s)
        self.assertTrue(replay(s, st.run()).rank_one_zero)
        self.assertEqual(s.max_length, 2)
        self.assertGreater(max(s.lengths()).bit_length(), 200)


if __name__ == '__main__':
    unittest.main()
