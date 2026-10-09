"""Independent oracles and maintained replay tests for raw saturation."""
import random
import unittest

from fastunknot.compressed_words import CompressedLimit, WordArena
from fastunknot.elimination_batch import apply_batch, plan_batch
from fastunknot.elimination_batch_verify import (
    replay_compressed_batch, replay_literal_batch,
)
from fastunknot.raw_saturation import build_index, find_rank_one_plan, seed_closure


def literal_closure(words, alive, seeds):
    known = set(seeds)
    while True:
        before = set(known)
        for word in words:
            support = {abs(x) for x in word}
            unknown = support - known
            if len(unknown) == 1:
                g = next(iter(unknown))
                if sum(abs(x) == g for x in word) == 1:
                    known.add(g)
        if before == known:
            return known


class LiteralBudget:
    def tick(self, amount=1):
        pass

    def size(self, amount):
        if amount > 1_000_000:
            raise RuntimeError('test literal allocation cap exceeded')


def make_arena(words):
    arena = WordArena(max_nodes=100_000, max_work=10_000_000)
    return arena, [arena.from_word(word) for word in words]


class RawSaturationTests(unittest.TestCase):
    def test_fixed_seed_closure_matches_literal_fixed_points(self):
        rng = random.Random(57831)
        for _ in range(400):
            rank = rng.randrange(1, 7)
            alive = set(range(1, rank + 1))
            words = [[rng.randrange(1, rank + 1) * rng.choice([-1, 1])
                      for _ in range(rng.randrange(8))]
                     for _ in range(rng.randrange(9))]
            arena, roots = make_arena(words)
            index = build_index(arena, roots, alive)
            nodes_before = len(arena.rules)
            for bits in range(1 << rank):
                seeds = {g for g in alive if bits & (1 << (g - 1))}
                got = seed_closure(arena, index, seeds)
                expected = literal_closure(words, alive, seeds)
                self.assertEqual(set(got.known), expected)
                self.assertEqual(got.complete, expected == alive)
                self.assertEqual(len({slot for slot, _ in got.entries}), len(got.entries))
                already = set(seeds)
                for slot, g in got.entries:
                    self.assertNotIn(g, already)
                    self.assertEqual(sum(abs(x) == g for x in words[slot]), 1)
                    self.assertLessEqual({abs(x) for x in words[slot]} - {g}, already)
                    already.add(g)
                self.assertEqual(already, expected)
            self.assertEqual(len(arena.rules), nodes_before)

    def test_all_seed_search_and_independent_existing_replay(self):
        rng = random.Random(476918)
        successes = 0
        for _ in range(600):
            rank = rng.randrange(2, 7)
            alive = set(range(1, rank + 1))
            words = [[rng.randrange(1, rank + 1) * rng.choice([-1, 1])
                      for _ in range(rng.randrange(1, 7))]
                     for _ in range(rng.randrange(1, 9))]
            arena, roots = make_arena(words)
            before = list(roots), set(alive), len(arena.rules)
            expected = next((g for g in sorted(alive)
                             if literal_closure(words, alive, {g}) == alive), None)
            plan = find_rank_one_plan(arena, roots, alive)
            self.assertEqual(None if plan is None else plan['seed'], expected)
            self.assertEqual((roots, alive, len(arena.rules)), before)
            if plan is None:
                continue
            successes += 1
            move = dict(kind='elimination_batch', entries=plan['entries'])
            checker, checked_roots = make_arena(words)
            checked_alive = set(alive)
            literal, literal_alive = [list(w) for w in words], set(alive)
            apply_batch(arena, roots, alive, plan['entries'])
            self.assertTrue(replay_compressed_batch(checker, checked_roots,
                                                   checked_alive, move))
            self.assertTrue(replay_literal_batch(literal, literal_alive, move,
                                                LiteralBudget()))
            self.assertEqual(alive, {plan['seed']})
            self.assertEqual(checked_alive, alive)
            self.assertEqual(literal_alive, alive)
            self.assertEqual([arena.expand(r) for r in roots], literal)
            self.assertEqual([checker.expand(r) for r in checked_roots], literal)
        self.assertGreater(successes, 50)

    def test_original_slots_empty_rows_and_duplicate_roots(self):
        words = [[], [1, 4], [1, 5], [], [1, 4]]
        arena, roots = make_arena(words)
        index = build_index(arena, roots, {1, 4, 5})
        result = seed_closure(arena, index, {4, 5})
        self.assertTrue(result.complete)
        self.assertEqual(result.entries, ((1, 1),))
        self.assertEqual(result.certificate_entries(), [dict(relation=1, generator=1)])

    def test_complete_closure_recovers_from_greedy_donor_obstruction(self):
        arena = WordArena(max_nodes=100_000, max_work=10_000_000)
        x, y, z, a = [arena.letter(g) for g in range(1, 5)]
        a10 = arena.power(a, 10)
        roots = [arena.from_word([1, 2, 3]),
                 arena.concat(arena.from_word([1, 3]), a10),
                 arena.concat(x, a10), arena.power(z, 1 << 64),
                 arena.power(arena.concat(y, arena.inverse(a10)), 1 << 64)]
        alive = {1, 2, 3, 4}
        self.assertEqual(plan_batch(arena, roots, alive),
                         [dict(relation=0, generator=1)])
        plan = find_rank_one_plan(arena, roots, alive)
        self.assertEqual(plan, dict(seed=4, entries=[dict(relation=2, generator=1),
                                                    dict(relation=1, generator=3),
                                                    dict(relation=0, generator=2)]))
        apply_batch(arena, roots, alive, plan['entries'])
        self.assertEqual(alive, {4})
        self.assertEqual([arena.reduce(root) for root in roots], [0] * 5)

    def test_raw_occurrences_do_not_use_exponents_or_free_reduction(self):
        # Both original source rows are freely reduced. After x <- y^-1,
        # the second becomes y^-1 y y; reduction would enable y, but raw
        # elimination cannot. This source has weighted permanent three.
        words = [[1, 2], [1, 2, 2]]
        arena, roots = make_arena(words)
        index = build_index(arena, roots, {1, 2, 3})
        self.assertEqual(seed_closure(arena, index, {3}).known, (3,))
        self.assertIsNone(find_rank_one_plan(arena, roots, {1, 2, 3}))
        # A repeated shared child contributes multiplicity two even though
        # only one grammar node holds the symbol.
        arena = WordArena()
        x, a = arena.letter(1), arena.letter(2)
        root = arena.concat(a, arena.concat(x, x))
        index = build_index(arena, [root], {1, 2})
        self.assertEqual(seed_closure(arena, index, {2}).known, (2,))

    def test_huge_shared_words_without_expansion(self):
        arena = WordArena(max_nodes=40_000, max_work=30_000_000)
        x, y, a = [arena.letter(g) for g in (1, 2, 3)]
        huge = arena.power(a, 1 << 4096)
        roots = [arena.concat(x, huge), arena.concat(y, arena.inverse(x)),
                 arena.concat(x, arena.inverse(y))]
        alive = {1, 2, 3}
        nodes = len(arena.rules)
        arena.expand = lambda *args, **kwargs: self.fail('discovery expanded a word')
        plan = find_rank_one_plan(arena, roots, alive)
        self.assertEqual(plan, dict(seed=3, entries=[dict(relation=0, generator=1),
                                                    dict(relation=1, generator=2)]))
        self.assertEqual(nodes, len(arena.rules))
        apply_batch(arena, roots, alive, plan['entries'])
        self.assertEqual(alive, {3})
        self.assertEqual(arena.reduce(roots[2]), 0)

    def test_cache_tracks_arena_roots_order_and_live_set(self):
        arena, roots = make_arena([[1, 2], [2, 3]])
        cache = {}
        first = find_rank_one_plan(arena, roots, {1, 2, 3}, cache)
        self.assertEqual(first['seed'], 1)
        self.assertEqual(arena.stats['raw_saturation_indices'], 1)
        self.assertEqual(find_rank_one_plan(arena, roots, {1, 2, 3}, cache), first)
        self.assertEqual(arena.stats['raw_saturation_indices'], 1)
        swapped = find_rank_one_plan(arena, list(reversed(roots)), {1, 2, 3}, cache)
        self.assertEqual(swapped['entries'][0]['relation'], 1)
        self.assertEqual(arena.stats['raw_saturation_indices'], 2)
        find_rank_one_plan(arena, roots, {1, 2, 3, 4}, cache)
        self.assertEqual(arena.stats['raw_saturation_indices'], 3)
        second, second_roots = make_arena([[1, 2], [2, 3]])
        self.assertEqual(find_rank_one_plan(second, second_roots, {1, 2, 3}, cache), first)
        self.assertEqual(second.stats['raw_saturation_indices'], 1)

    def test_first_firing_guard_is_exact_and_does_not_skip_unary_rules(self):
        words = [[1, 2, 3], [2, 3, 4], [1, 4, 4, 1]]
        arena, roots = make_arena(words)
        self.assertIsNone(find_rank_one_plan(arena, roots, {1, 2, 3, 4}))
        self.assertEqual(arena.stats['raw_saturation_first_firing_failures'], 1)
        self.assertEqual(arena.stats.get('raw_saturation_seed_attempts', 0), 0)
        self.assertEqual(arena.stats.get('raw_saturation_indices', 0), 0)
        # Even a rejected source must be checked against the entire live
        # alphabet; the guard must not hide a non-live label in a later row.
        with self.assertRaises(ValueError):
            find_rank_one_plan(arena, roots, {1, 2, 3})
        # Cached masks avoid calling the list-producing singleton interface
        # again when the exact guard can already decide the source.
        arena.singletons = lambda *args: self.fail('cached guard decoded singletons')
        self.assertIsNone(find_rank_one_plan(arena, roots, {1, 2, 3, 4}))
        # Empty-premise source rule x=1 can start closure from any other seed.
        arena, roots = make_arena([[1], [1, 2, 3]])
        plan = find_rank_one_plan(arena, roots, {1, 2, 3})
        self.assertEqual(plan['seed'], 2)
        self.assertEqual(plan['entries'][0], dict(relation=0, generator=1))
        self.assertEqual(arena.stats.get('raw_saturation_first_firing_failures', 0), 0)

    def test_strict_arguments_attempt_cap_and_nonlive_source(self):
        arena, roots = make_arena([[1, 2]])
        for cap in [-1, True, 1.5]:
            with self.assertRaises(ValueError):
                find_rank_one_plan(arena, roots, {1, 2}, max_attempts=cap)
        self.assertIsNone(find_rank_one_plan(arena, roots, {1, 2}, max_attempts=0))
        for live in [[1, True], [1, 1], [0, 1], []]:
            with self.assertRaises(ValueError):
                find_rank_one_plan(arena, roots, live)
        with self.assertRaises(ValueError):
            build_index(arena, roots, {1})
        with self.assertRaises(ValueError):
            find_rank_one_plan(arena, [True], {1, 2})
        with self.assertRaises(ValueError):
            find_rank_one_plan(arena, roots, {1, 2}, cache=[])
        index = build_index(arena, roots, {1, 2})
        for seeds in [[True], [1, 1], [3]]:
            with self.assertRaises(ValueError):
                seed_closure(arena, index, seeds)

    def test_resource_and_external_cancellation_preserve_source(self):
        words = [[g, g + 1] for g in range(1, 40)]
        for failure in ['work', 'cancel']:
            arena, roots = make_arena(words)
            alive = set(range(1, 41))
            before = list(roots), set(alive), len(arena.rules)
            if failure == 'work':
                arena.left = 23
                exception = CompressedLimit
            else:
                seen = [0]
                def cancel():
                    seen[0] += 1
                    if seen[0] == 23:
                        raise ValueError('external cancellation')
                arena.check = cancel
                exception = ValueError
            with self.assertRaises(exception):
                find_rank_one_plan(arena, roots, alive)
            self.assertEqual((roots, alive, len(arena.rules)), before)
            arena.check = lambda: None
            arena.left = 1_000_000
            self.assertIsNotNone(find_rank_one_plan(arena, roots, alive))


if __name__ == '__main__':
    unittest.main()
