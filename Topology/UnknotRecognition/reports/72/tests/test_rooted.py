from __future__ import annotations
import copy
import itertools
import random
import unittest
from unittest.mock import patch
from rooted_disc.kernel import (State, Candidate, ResourceLimit, feature, pairing,
    direct_compatibility, decorated_states, partitions, reduce_candidates, star_states, binary_rank)
from rooted_disc.verify import reference_feature, verify_reduction
from rooted_disc.search_verify import verify_search, reference_transition
from rooted_disc.assembly import Patch, Grammar, solve, transition, enumerate_assignments
from rooted_disc.mesh import replay_pair, replay_assignment
from experiments.common import operation, workload, random_grammar


class SyntaxTests(unittest.TestCase):
    def test_noncanonical_partition(self):
        for p in [(), (1,), (0, 2), (False,)]:
            with self.assertRaises(ValueError): State(p, (True,), (0,))
    def test_charge_group(self):
        for q in [0, -1, 3, True]:
            with self.assertRaises(ValueError): State((0,), (True,), (0,), q)
    def test_block_lengths(self):
        with self.assertRaises(ValueError): State((0, 1), (True,), (0,))
    def test_bad_charge_canonical(self):
        with self.assertRaises(ValueError): State((0,), (False,), (1,), 4)
    def test_flags_and_cost_types(self):
        with self.assertRaises(ValueError): State((0,), (1,), (0,))
        with self.assertRaises(ValueError): Candidate(State((0,), (True,), (0,)), True)
    def test_json_roundtrip(self):
        s = State((0, 1, 0), (True, False), (2, 0), 4)
        self.assertEqual(State.from_dict(s.as_dict()), s)
    def test_interface_mismatch(self):
        a = State((0,), (True,), (0,))
        b = State((0, 0), (True,), (0,))
        with self.assertRaises(ValueError): pairing(a, b)
        with self.assertRaises(ValueError): reduce_candidates([Candidate(a, 0), Candidate(b, 0)])
    def test_limits_are_not_negative_answers(self):
        s = State(tuple(range(10)), (True,) * 10, (0,) * 10)
        with self.assertRaises(ResourceLimit): feature(s, 100)
        with self.assertRaises(ResourceLimit): solve(workload(2, 1), max_transitions=0)
    def test_patch_arity(self):
        with self.assertRaises(ValueError): Patch(1, 1, (0,), (True,), (0,))
    def test_unconsumed_terminal(self):
        c = Candidate(State((0, 1), (True, True), (0, 0)), 0)
        with self.assertRaises(ValueError): Grammar((c,), (), 0)


class KernelTests(unittest.TestCase):
    def test_rank_one_interface(self):
        s = State((0,), (True,), (2,), 4)
        t = State((0,), (True,), (1,), 4)
        self.assertTrue(pairing(s, t, 3)); self.assertTrue(pairing(s, t, None))
        self.assertFalse(pairing(s, t, 0))
    def test_bad_root_zero(self):
        s = State((0, 1), (False, True), (0, 0))
        self.assertEqual(feature(s), 0)
    def test_unrelated_annulus_allowed(self):
        s = State((0, 1), (True, False), (0, 0))
        t = State((0, 1), (True, True), (0, 0))
        self.assertTrue(pairing(s, t))
        self.assertEqual(replay_pair(s, t).root_euler, 1)
    def test_unrelated_cycle_allowed(self):
        s = State((0, 1, 1), (True, True), (0, 0))
        self.assertTrue(pairing(s, s))
        m = replay_pair(s, s)
        self.assertEqual(sorted(x[0] for x in m.components), [0, 1])
    def test_root_cycle_rejected(self):
        s = State((0, 0), (True,), (0,))
        self.assertFalse(pairing(s, s)); self.assertEqual(replay_pair(s, s).root_euler, 0)
    def test_component_local_charge(self):
        s = State((0, 1), (True, True), (1, 1), 4)
        t = State((0, 1), (True, True), (0, 0), 4)
        self.assertEqual(s.charges[0] ^ s.charges[1], 0)
        self.assertTrue(pairing(s, t, None))
    def test_exhaustive_small_rows_and_pairings(self):
        for r in range(1, 4):
            states = list(decorated_states(r))
            for s in states:
                self.assertEqual(feature(s), reference_feature(s))
                for t in states:
                    self.assertEqual(pairing(s, t), direct_compatibility(s, t))
    def test_charged_pairing(self):
        states = list(decorated_states(3, 4))
        rng = random.Random(21)
        for _ in range(1000):
            s, t = rng.choice(states), rng.choice(states)
            for target in (None, 0, 1, 2, 3):
                self.assertEqual(pairing(s, t, target), direct_compatibility(s, t, target))
    def test_exact_ternary_rank(self):
        for r in range(1, 5):
            rows = [s for s, _, _ in star_states(r)]
            self.assertEqual(binary_rank(feature(s) for s in rows), 3 ** (r - 1))
            self.assertEqual(binary_rank(sum(int(direct_compatibility(s, t)) << i for i, t in enumerate(rows)) for s in rows), 3 ** (r - 1))
    def test_nonzero_charge_rank(self):
        states = [s for s, _, _ in star_states(3, 4)]
        self.assertEqual(binary_rank(sum(int(direct_compatibility(s, t, None)) << i for i, t in enumerate(states)) for s in states), 36)
    def test_sparse_support_product(self):
        s = State((0, 1, 1, 2, 2, 2, 3), (True, True, True, False), (0, 0, 0, 0))
        self.assertEqual(feature(s).bit_count(), 3 * 4)


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.family = [Candidate(s, 100 - i, (i,)) for i, s in enumerate(decorated_states(4))]
        self.kept, self.cert = reduce_candidates(self.family, geometry_key="mesh-source-A")
    def test_independent_checker(self):
        with patch("rooted_disc.kernel.feature", side_effect=AssertionError("producer called")):
            self.assertTrue(verify_reduction(self.family, self.cert, geometry_key="mesh-source-A"))
    def test_wrong_source_key(self):
        self.assertFalse(verify_reduction(self.family, self.cert, geometry_key="mesh-source-B"))
    def test_cost_tamper(self):
        changed = self.family.copy(); c = changed[0]
        changed[0] = Candidate(c.state, c.cost + 1, c.witness)
        self.assertFalse(verify_reduction(changed, self.cert, geometry_key="mesh-source-A"))
    def test_expression_tamper(self):
        c = copy.deepcopy(self.cert); c["expressions_hex"][0] = "0x0"
        self.assertFalse(verify_reduction(self.family, c, geometry_key="mesh-source-A"))
    def test_kept_tamper(self):
        c = copy.deepcopy(self.cert); c["kept"][0] = -1
        self.assertFalse(verify_reduction(self.family, c, geometry_key="mesh-source-A"))
    def test_empty_family(self):
        kept, c = reduce_candidates([], geometry_key="empty")
        self.assertEqual(kept, []); self.assertTrue(verify_reduction([], c, geometry_key="empty"))
    def test_large_negative_costs(self):
        family = [Candidate(s, (-1) ** i * (1 << 300) + i) for i, s in enumerate(decorated_states(3))]
        kept, c = reduce_candidates(family)
        self.assertTrue(verify_reduction(family, c, geometry_key="abstract"))
        for t in decorated_states(3):
            opt = lambda f: min((x.cost for x in f if direct_compatibility(x.state, t)), default=None)
            self.assertEqual(opt(family), opt(kept))
    def test_twenty_thousand_bit_cost_encoding(self):
        s = State((0,), (True,), (0,))
        family = [Candidate(s, -(1 << 20000)), Candidate(s, 1 << 20000)]
        kept, c = reduce_candidates(family)
        self.assertTrue(verify_reduction(family, c, geometry_key="abstract"))
        self.assertEqual(int(family[0].as_dict()["cost"], 16), family[0].cost)
        g = Grammar((family[0],), (), 0)
        self.assertEqual(Grammar.from_dict(g.as_dict()), g)
    def test_weighted_sharpness(self):
        family = [(s, c, w) for s, c, w in star_states(3, 4)]
        by_key = {(w, s.charges[0]): s for s, c, w in family}
        for state, cost, word in family:
            query_word = tuple({"R": "G", "B": "B", "G": "R"}[x] for x in word)
            t = by_key[query_word, state.charges[0]]
            feasible = [(c, s) for s, c, _ in family if direct_compatibility(s, t, 0)]
            minimum = min(c for c, _ in feasible)
            self.assertEqual([s for c, s in feasible if c == minimum], [state])


class AssemblyTests(unittest.TestCase):
    def test_forget_bad_nonroot(self):
        s = State((0, 0, 1), (True, False), (1, 0), 4)
        cap = Patch(2, 0, (0, 1), (True, True), (0, 0), 0, 4)
        out = transition(s, cap)
        self.assertEqual(out, State((0,), (True,), (1,), 4))
    def test_bad_join_reaches_root(self):
        s = State((0, 0, 1), (True, False), (1, 0), 4)
        out = transition(s, operation(2, 4, "join", 0, 1))
        self.assertFalse(out.good[0])
    def test_grammar_roundtrip(self):
        g = workload(2, 2)
        self.assertEqual(Grammar.from_dict(g.as_dict()), g)
        self.assertEqual(Grammar.from_dict(g.as_dict()).digest(), g.digest())
    def test_rooted_workload_both_solvers(self):
        g = workload(3, 4)
        a, b = solve(g, reduced=False), solve(g, reduced=True, certificates=True)
        self.assertEqual((a.status, a.cost), (b.status, b.cost))
        self.assertTrue(replay_assignment(g, b.witness).succeeds(g.target))
        for record in b.reductions:
            family = [Candidate(State.from_dict(x["state"]), int(x["cost"], 16), tuple(x["witness"])) for x in record["candidates"]]
            c = record["certificate"]
            self.assertTrue(verify_reduction(family, c, geometry_key=c["geometry_key"]))
    def test_literal_small_languages(self):
        rng = random.Random(13)
        for _ in range(12):
            g = random_grammar(rng, layers=2, options=2)
            costs = [m.cost for w in enumerate_assignments(g) for m in [replay_assignment(g, w)] if m.succeeds(g.target)]
            expected = min(costs, default=None)
            self.assertEqual(solve(g, reduced=False).cost, expected)
            self.assertEqual(solve(g, reduced=True).cost, expected)
    def test_mesh_both_orientation_maps(self):
        states = list(decorated_states(3, 4))
        rng = random.Random(73)
        for _ in range(30):
            a, b = rng.choice(states), rng.choice(states)
            for flips in itertools.product((False, True), repeat=3):
                m = replay_pair(a, b, flips)
                self.assertEqual(m.succeeds(None), direct_compatibility(a, b, None))
    def test_independent_complete_search_replay(self):
        g = workload(3, 3)
        answer = solve(g, certificates=True).as_dict()
        with patch("rooted_disc.assembly.transition", side_effect=AssertionError("producer transition called")), patch("rooted_disc.assembly.solve", side_effect=AssertionError("producer search called")), patch("rooted_disc.kernel.feature", side_effect=AssertionError("producer features called")):
            self.assertTrue(verify_search(g, answer))
    def test_complete_search_negative_and_tampered_verdict(self):
        g = Grammar((Candidate(State((0,), (True,), (0,), 4), 0),), (), None)
        answer = solve(g, certificates=True).as_dict()
        self.assertTrue(verify_search(g, answer))
        answer['status'] = 'FOUND_ABSTRACT_ROOTED_DISC'
        self.assertFalse(verify_search(g, answer))
    def test_omitted_option_generation_rejected(self):
        g = workload(2, 2)
        answer = solve(g, certificates=True).as_dict()
        record = answer['reductions'][1]
        source = [Candidate(State.from_dict(x['state']), int(x['cost'], 16), tuple(x['witness'])) for x in record['candidates']][1:]
        # Even fresh, valid linear evidence cannot excuse omitted local candidates.
        _, cert = reduce_candidates(source, geometry_key=record['certificate']['geometry_key'])
        record['candidates'] = [c.as_dict() for c in source]
        record['certificate'] = cert
        self.assertFalse(verify_search(g, answer))
    def test_reference_transition_all_small_pairs(self):
        for s in decorated_states(3, 1, root_good=False):
            for t in decorated_states(4, 1, root_good=False):
                p = Patch(2, 2, t.partition, t.good, t.charges)
                self.assertEqual(transition(s, p), reference_transition(s, p))
    def test_malformed_witness_rejected(self):
        g = workload(2, 1)
        with self.assertRaises(ValueError): replay_assignment(g, (-1, 0, 0))
    def test_inconclusive_limits(self):
        g = workload(3, 2)
        with self.assertRaises(ResourceLimit): solve(g, max_dimension=1)


if __name__ == "__main__":
    unittest.main()
