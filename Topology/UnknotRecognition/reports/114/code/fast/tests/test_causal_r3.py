"""Actual-diagram oracles, rollback, and recognition checks for causal RIII."""
import itertools
import json
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.causal_r3 import footprint, search_clustered_unlock, _candidates
from fastunknot.simplify import _Darts, _unlock, replay, simplify


def state_for(diagram, budget=float("inf")):
    state = _Darts(diagram)
    state.trials, state.budget = 0, budget
    return state


def oracle(state, depth, births_left, active=frozenset()):
    """All legal faces everywhere, no birth ordering, no inverse/cycle pruning."""
    if not depth:
        return False
    faces = {frozenset(t): t for d in range(4 * len(state.alive))
             if (t := state.triangle_at(d)) is not None}
    for triangle in faces.values():
        support = footprint(state, triangle)
        born = active.isdisjoint(support)
        if born and not births_left:
            continue
        before = state.alpha[:]
        try:
            if state.apply_r3(triangle) is None:
                continue
            if any(state.move_at(d) is not None for d in range(len(state.alpha))):
                return True
            if oracle(state, depth - 1, births_left - born, active | support):
                return True
        finally:
            state.alpha[:] = before
    return False


def corpus():
    words = [(3, [1, 2] * m) for m in (2, 4, 5, 7)]
    words += [(3, [-2, -2, -2, 2, 1, 1, 2, 1]),
              (4, [2, -1, 2, -3, -1, 3, -1, -2, -1, 1, 3, -2, 3]),
              (4, [-3, -2, 3, 3, 1, 2, -2, 2, -3, 1, 1, -2, -2, -2, -2, -1, 3, 2, 2])]
    rng = random.Random(2702)
    words += [(s, [rng.choice((-1, 1)) * rng.randrange(1, s) for _ in range(15)])
              for s in [4] * 70]
    for s, word in words:
        try:
            diagram = Diagram.from_braid(s, word)
        except ValueError:
            continue
        reduced, _ = simplify(diagram, r3=False)
        if reduced.crossings >= 3:
            yield reduced


class CausalR3Tests(unittest.TestCase):
    def test_complete_against_unrestricted_small_oracle(self):
        successes = failures = comparisons = 0
        for diagram in corpus():
            for depth, births in itertools.product((1, 2, 3), (1, 2)):
                expected = oracle(state_for(diagram), depth, births)
                for check_faces in (False, True):
                    state, path = state_for(diagram), []
                    before = state.alpha[:]
                    found = search_clustered_unlock(state, depth, max_births=births,
                                                    check_faces=check_faces, path=path)
                    self.assertEqual(found is not None, expected,
                                     (diagram.pd, depth, births, check_faces))
                    if found is None:
                        self.assertEqual(state.alpha, before)
                        self.assertEqual(path, [])
                        failures += 1
                    else:
                        self.assertLessEqual(len(path), depth)
                        self.assertTrue(any(state.move_at(d) is not None for d in found))
                        records = [{"kind": "R3", "crossings": sorted(d // 4 for d in t),
                                    "triangle": t} for t in path]
                        self.assertEqual(replay(diagram, records).pd, state.rebuild().pd)
                        successes += 1
                    comparisons += 1
        self.assertGreater(comparisons, 100)
        self.assertGreater(successes, 10)
        self.assertGreater(failures, 10)

    def test_disjoint_births_commute_on_actual_darts(self):
        state = state_for(Diagram.from_braid(3, [1, 2] * 11))
        first = next(_candidates(state, frozenset(), 0, True, None, 2, None))
        t1, f1, _, _, key = first
        before = state.alpha[:]
        self.assertIsNotNone(state.apply_r3(t1))
        self.assertEqual(footprint(state, t1), f1)
        second = next(c for c in _candidates(state, f1, 1, True, key, 2, None)
                      if c[3] and f1.isdisjoint(c[1]))
        t2 = second[0]
        self.assertIsNotNone(state.apply_r3(t2))
        after = state.alpha[:]
        state.alpha[:] = before
        self.assertIsNotNone(state.apply_r3(t2))
        self.assertIsNotNone(state.apply_r3(t1))
        self.assertEqual(state.alpha, after)

    def test_trial_limits_restore_failed_searches(self):
        diagram = Diagram.from_braid(3, [1, 2] * 4)
        for budget in (0, 1, 2, 3, 9, 30):
            state, path = state_for(diagram, budget), ["prefix"]
            before = state.alpha[:]
            self.assertIsNone(search_clustered_unlock(state, 4, path=path))
            self.assertLessEqual(state.trials, budget)
            self.assertEqual(state.alpha, before)
            self.assertEqual(path, ["prefix"])

    def test_inverse_retained_when_previous_move_added_support(self):
        state = state_for(Diagram.from_braid(3, [1, 2] * 4))
        before, path, observed = state.alpha[:], [], []

        def check():
            if len(path) == 2 and state.alpha == before:
                observed.append(tuple(path))

        self.assertIsNone(search_clustered_unlock(state, 2, path=path, check=check,
                                                  check_faces=False))
        self.assertTrue(observed)
        self.assertEqual(state.alpha, before)

    def test_nested_cancellation_rolls_back_both_searches(self):
        diagram = Diagram.from_braid(3, [1, 2] * 4)
        for mode in ("last", "clustered"):
            for stop in (1, 2, 3, 7):
                state, path = state_for(diagram), ["prefix"]
                before = state.alpha[:]

                def check():
                    if state.trials >= stop:
                        raise InterruptedError("test cancellation")

                with self.assertRaises(InterruptedError):
                    if mode == "last":
                        _unlock(state, 4, range(len(state.alpha)), None, path, False, check)
                    else:
                        search_clustered_unlock(state, 4, check_faces=False, path=path, check=check)
                self.assertEqual(state.alpha, before)
                self.assertEqual(path, ["prefix"])
                self.assertEqual(state.trials, stop)

    def test_exception_during_mutation_restores_journal(self):
        state = state_for(Diagram.from_braid(3, [1, 2] * 4))
        before, path = state.alpha[:], []

        def broken_apply(triangle):
            state.alpha[triangle[0]] = triangle[0]
            raise ArithmeticError("injected failure")

        state.apply_r3 = broken_apply
        with self.assertRaises(ArithmeticError):
            search_clustered_unlock(state, 2, path=path, check_faces=False)
        self.assertEqual(state.alpha, before)
        self.assertEqual(path, [])

    def test_adaptive_allowance_and_precise_replay(self):
        diagram = Diagram.from_braid(3, [1, 2] * 4)
        stats = {}
        reduced, trace = simplify(diagram, r3_search="adaptive", r3_budget=2, stats=stats)
        self.assertEqual(replay(diagram, trace).pd, reduced.pd)
        self.assertGreater(stats["last_trials"], 0)
        self.assertGreater(stats["clustered_trials"], 0)
        self.assertEqual(stats["switches"], 1)
        self.assertLessEqual(stats["last_trials"] + stats["clustered_trials"], 2 * diagram.crossings)
        hard = Diagram.from_braid(3, [-2, -2, -2, 2, 1, 1, 2, 1])
        for mode in ("last", "clustered", "adaptive"):
            for budget in (0, 1, 10, None):
                reduced, trace = simplify(hard, r3_search=mode, r3_budget=budget)
                self.assertEqual(replay(hard, json.loads(json.dumps([m.to_json() for m in trace]))).pd,
                                 reduced.pd)
                if budget == 0:
                    self.assertEqual(reduced.pd, simplify(hard, r3=False)[0].pd)
                else:
                    self.assertEqual(reduced.crossings, 0)

    def test_recognition_global_deadline_interrupts_trials(self):
        hard = Diagram.from_braid(3, [-2, -2, -2, 2, 1, 1, 2, 1])
        original_apply = _Darts.apply_r3
        for mode in ("last", "clustered", "adaptive"):
            captured = []

            def applying(state, triangle):
                if not captured:
                    captured.append((state, state.alpha[:]))
                return original_apply(state, triangle)

            with patch.object(_Darts, "apply_r3", applying), patch(
                    "fastunknot.recognize.monotonic", side_effect=lambda: 2 if captured else 0):
                result = recognize(hard, seconds=1, use_braid=False, use_seifert=False,
                                   use_braid_reduction=False, use_descending=False,
                                   use_modular=False, use_jones=False, use_alexander=False,
                                   use_factorization=False, r3_search=mode)
            self.assertEqual(result.status, "UNKNOWN")
            self.assertTrue(captured)
            self.assertEqual(captured[0][0].alpha, captured[0][1])

    def test_invalid_options_are_rejected_before_early_certificates(self):
        empty = Diagram.from_pd([])
        for options in ({"r3_search": "unknown"}, {"r3_depth": 0}, {"r3_depth": True},
                        {"r3_births": 0}, {"r3_births": 1.0}, {"r3_budget": -1},
                        {"r3_budget": False}, {"r3_budget": float("inf")}):
            for call in (simplify, recognize):
                with self.subTest(options=options, call=call), self.assertRaises(ValueError):
                    call(empty, **options)

    def test_no_first_move_stops_deepening_and_switching(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for mode in ("last", "adaptive"):
            with patch("fastunknot.simplify._unlock", wraps=_unlock) as calls, patch(
                    "fastunknot.causal_r3.search_clustered_unlock",
                    side_effect=AssertionError("no sequence can start")):
                result, trace = simplify(diagram, r3_search=mode, r3_depth=1000,
                                         r3_budget=None)
            self.assertEqual([call.args[1] for call in calls.call_args_list], [1, 2])
            self.assertEqual(result.pd, diagram.pd)
            self.assertEqual(trace, [])

    def test_deeper_search_exposes_existing_hard_unknot(self):
        from hard_unknots import SURVIVORS
        _, strands, word = SURVIVORS[1]
        diagram = Diagram.from_braid(strands, word)
        self.assertEqual(simplify(diagram)[0].crossings, 15)
        stats = {}
        reduced, trace = simplify(diagram, r3_depth=6, stats=stats)
        self.assertEqual(reduced.crossings, 0)
        self.assertEqual(replay(diagram, trace).pd, reduced.pd)
        self.assertLess(stats["last_trials"], 40)
        result = recognize(diagram, r3_depth=6)
        self.assertEqual((result.status, result.method), ("UNKNOT", "reidemeister-reduction"))


if __name__ == "__main__":
    unittest.main()
