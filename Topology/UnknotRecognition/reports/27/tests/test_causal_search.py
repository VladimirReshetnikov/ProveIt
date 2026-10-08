from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from prototype.causal_search import (  # noqa: E402
    BooleanLocalSystem,
    Move,
    Reduction,
    accumulated_strict_example,
    birth_front_unlock,
    birth_number,
    branching_example,
    dependency_graph,
    frontload_births,
    graph_connected,
    last_touch_unlock,
    replay,
    shortest_unlock_bfs,
    support_history_example,
    truncate_at_first_reduction,
)


def random_system(rng: random.Random, n_sites: int = 6) -> BooleanLocalSystem:
    moves: list[Move] = []
    for index in range(9):
        target = rng.randrange(n_sites)
        candidates = [site for site in range(n_sites) if site != target]
        rng.shuffle(candidates)
        guard_sites = candidates[: rng.randrange(0, min(2, n_sites - 1) + 1)]
        guard = tuple(sorted((site, rng.randrange(2)) for site in guard_sites))
        support = frozenset({target, *guard_sites})
        moves.append(Move(f"m{index:02d}", support, frozenset({target}), guard))

    reductions: list[Reduction] = []
    for index in range(3):
        size = rng.randrange(1, min(3, n_sites + 1))
        sites = sorted(rng.sample(range(n_sites), size))
        required = tuple((site, rng.randrange(2)) for site in sites)
        reductions.append(Reduction(f"r{index}", frozenset(sites), required))
    return BooleanLocalSystem(n_sites, tuple(moves), tuple(reductions))


class CausalSearchTests(unittest.TestCase):
    def test_two_birth_branching_example(self) -> None:
        system, initial = branching_example()
        oracle = shortest_unlock_bfs(system, initial, 4)
        self.assertEqual(oracle.trace, ("A", "B", "C"))
        self.assertEqual(birth_number(system, oracle.trace), 2)
        self.assertFalse(birth_front_unlock(system, initial, 4, 1).found)
        found = birth_front_unlock(system, initial, 4, 2)
        self.assertTrue(found.found)
        self.assertEqual(len(found.trace or ()), 3)
        _, reduction = replay(system, initial, found.trace or (), require_first_unlock=True)
        self.assertEqual(reduction, "R")
        graph = dependency_graph(system, found.trace or (), "R")
        self.assertTrue(graph_connected(graph))

    def test_accumulated_support_strictly_beats_last_touch(self) -> None:
        system, initial = accumulated_strict_example()
        oracle = shortest_unlock_bfs(system, initial, 4)
        self.assertTrue(oracle.found)
        self.assertEqual(len(oracle.trace or ()), 3)
        self.assertEqual(birth_number(system, oracle.trace or ()), 1)
        self.assertFalse(last_touch_unlock(system, initial, 4).found)
        accumulated = birth_front_unlock(system, initial, 4, 1)
        self.assertTrue(accumulated.found)
        self.assertEqual(len(accumulated.trace or ()), 3)

    def test_support_history_is_not_pruned_by_physical_state(self) -> None:
        system, initial = support_history_example()
        oracle = shortest_unlock_bfs(system, initial, 4)
        self.assertTrue(oracle.found)
        self.assertEqual(len(oracle.trace or ()), 2)
        self.assertEqual(birth_number(system, oracle.trace or ()), 2)
        bounded = birth_front_unlock(system, initial, 4, 1)
        self.assertTrue(bounded.found)
        self.assertEqual(len(bounded.trace or ()), 4)
        self.assertEqual(birth_number(system, bounded.trace or ()), 1)
        state = initial
        states = [state]
        for name in bounded.trace or ():
            state = system.move_by_name(name).apply(state)
            states.append(state)
        self.assertLess(len(set(states)), len(states))

    def test_frontloading_preserves_or_shortens_unlocking(self) -> None:
        system, initial = branching_example()
        trace = ("A", "B", "C")
        front = frontload_births(system, trace)
        truncated = truncate_at_first_reduction(system, initial, front)
        self.assertLessEqual(len(truncated), len(trace))
        _, reduction = replay(system, initial, truncated, require_first_unlock=True)
        self.assertEqual(reduction, "R")

    def test_random_finite_oracle_completeness(self) -> None:
        checked = 0
        for seed in range(200):
            rng = random.Random(seed)
            system = random_system(rng)
            initial = rng.randrange(1 << system.n_sites)
            if system.legal_reductions(initial):
                continue
            oracle = shortest_unlock_bfs(system, initial, 6)
            if not oracle.found:
                continue
            trace = oracle.trace or ()
            births = birth_number(system, trace)
            front = truncate_at_first_reduction(
                system, initial, frontload_births(system, trace)
            )
            _, reduction = replay(system, initial, front, require_first_unlock=True)
            self.assertIsNotNone(reduction)
            self.assertLessEqual(len(front), len(trace))
            search = birth_front_unlock(system, initial, len(trace), births)
            self.assertTrue(search.found, msg=f"seed={seed}, trace={trace}, births={births}")
            self.assertLessEqual(len(search.trace or ()), len(trace))
            checked += 1
        self.assertGreater(checked, 25)


if __name__ == "__main__":
    unittest.main()
