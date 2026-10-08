from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from integration.clustered_r3_snippet import (  # noqa: E402
    ClusterSearchStats,
    r3_footprint,
    search_clustered_unlock,
)


class MiniDarts:
    """A twelve-dart RIII gadget using the reviewed `_Darts` formulas.

    The initial involution contains the triangular face (1, 4, 8).  This is not
    offered as a spherical knot diagram; it is a narrow executable contract test
    for triangle discovery, the RIII involution, footprint stability, undo, and
    the adapter's success/failure state semantics.
    """

    def __init__(self, *, terminal_after_move: bool) -> None:
        self.alpha = [0] * 12
        for left, right in ((0, 8), (1, 7), (2, 5), (3, 6), (4, 11), (9, 10)):
            self.alpha[left] = right
            self.alpha[right] = left
        self.initial_alpha = tuple(self.alpha)
        self.alive = [True, True, True]
        self.remaining = 3
        self.trials = 0
        self.budget = 200
        self.terminal_after_move = terminal_after_move

    def nxt(self, dart: int) -> int:
        partner = self.alpha[dart]
        return partner - partner % 4 + (partner + 1) % 4

    def triangle_at(self, dart: int):
        if not self.alive[dart // 4]:
            return None
        second = self.nxt(dart)
        third = self.nxt(second)
        if self.nxt(third) != dart:
            return None
        if len({dart // 4, second // 4, third // 4}) != 3:
            return None
        if not any(
            item % 2 == 1 and self.alpha[item] % 2 == 1
            for item in (dart, second, third)
        ):
            return None
        return (dart, second, third)

    def apply_r3(self, triangle):
        alpha = self.alpha
        inner = [alpha[dart] for dart in triangle]
        entry_old = [dart ^ 2 for dart in triangle]
        exit_old = [dart ^ 2 for dart in inner]
        moved = {}
        for index in range(3):
            moved[entry_old[index]] = inner[index]
            moved[exit_old[index]] = triangle[index]
        if len(moved) != 6:
            return None
        links = []
        for dart, new_dart in moved.items():
            partner = alpha[dart]
            new_partner = moved.get(partner, partner)
            if new_partner == new_dart:
                return None
            links.append((new_dart, new_partner))
        for index in range(3):
            links.append((exit_old[index], entry_old[index]))
        for left, right in links:
            alpha[left] = right
            alpha[right] = left
        return [endpoint for link in links for endpoint in link]

    def r3_can_help(self, triangle) -> bool:
        return True

    def move_at(self, dart: int):
        if self.terminal_after_move and tuple(self.alpha) != self.initial_alpha:
            return ("R1", (dart // 4,), (dart,))
        return None


class ClusteredAdapterTests(unittest.TestCase):
    def test_failure_restores_exact_involution(self) -> None:
        state = MiniDarts(terminal_after_move=False)
        before = tuple(state.alpha)
        path: list[tuple[int, int, int]] = []
        stats = ClusterSearchStats()
        found = search_clustered_unlock(
            state,
            3,
            max_births=2,
            check_faces=True,
            path=path,
            stats=stats,
        )
        self.assertIsNone(found)
        self.assertEqual(tuple(state.alpha), before)
        self.assertEqual(path, [])
        self.assertGreater(stats.trial_moves, 0)

    def test_success_leaves_move_applied_and_replayable_inverse(self) -> None:
        state = MiniDarts(terminal_after_move=True)
        triangle = state.triangle_at(1)
        self.assertEqual(triangle, (1, 4, 8))
        before_footprint = r3_footprint(state, triangle)
        path: list[tuple[int, int, int]] = []
        found = search_clustered_unlock(
            state,
            1,
            max_births=1,
            check_faces=True,
            path=path,
        )
        self.assertIsNotNone(found)
        self.assertEqual(len(path), 1)
        self.assertNotEqual(tuple(state.alpha), state.initial_alpha)
        inverse = state.triangle_at(path[0][0] ^ 2)
        self.assertIsNotNone(inverse)
        after_footprint = r3_footprint(state, inverse)
        self.assertEqual(before_footprint, after_footprint)
        self.assertIsNotNone(state.apply_r3(inverse))
        self.assertEqual(tuple(state.alpha), state.initial_alpha)


if __name__ == "__main__":
    unittest.main()
