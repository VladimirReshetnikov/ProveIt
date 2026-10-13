import copy
import random
import unittest
from cycleblocks import *
from cycleblocks.powers import periodic_path_table
from tests.oracles import (brute_private, arbitrary_positive_optimum, literal_transport,
                      path_oracle, cycle_counts, cactus_counts, spanning_forests)


class MatrixTests(unittest.TestCase):
    def compare(self, counts, weights=None, allowed=None):
        want = brute_private(counts, weights, allowed)
        for pre in (False, True):
            plan = optimize_counts(counts, weights, allowed=allowed, prepeel=pre)
            self.assertEqual(plan['status'], 'OPTIMAL_MATRIX_PLAN')
            self.assertEqual(plan['matched_weight'], want)
            self.assertTrue(verify_plan(counts, plan, weights, allowed=allowed))
        return plan

    def test_empty(self): self.compare({})
    def test_empty_rows(self): self.compare({4: {}, 8: {}}, {4: 3, 8: 10})
    def test_single_unit(self): self.compare({9: {100: 1}})
    def test_only_nonunits(self): self.compare({0: {0: 2, 1: 7}, 1: {0: 3}})
    def test_tree_weights(self): self.compare({0: {0: 1, 1: 1}, 1: {1: 1}}, {0: 7, 1: 5})
    def test_even_cycle(self): self.compare(cycle_counts(5))
    def test_cactus_articulation_column(self): self.compare(cactus_counts(4))
    def test_cactus_weighted(self): self.compare(*cactus_counts(4, weights=True))
    def test_articulation_row(self):
        self.compare({0: {0: 1, 1: 1, 2: 1, 3: 1}, 1: {0: 1, 1: 1}, 2: {2: 1, 3: 1}})
    def test_k33(self): self.compare({r: {c: 1 for c in range(3)} for r in range(3)})
    def test_nonunit_blocks_alternation(self): self.compare({0: {0: 1, 1: 2}, 1: {0: 2, 1: 1}})
    def test_two_support_asymmetric(self): self.compare({0: {0: 1, 1: 1}, 1: {0: 1, 1: 2}})
    def test_restricted_units(self):
        self.compare({0: {0: 1, 1: 1}, 1: {0: 1, 1: 1}}, allowed={(0, 0)})
    def test_zero_weights(self): self.compare(cactus_counts(2), {i: 0 for i in range(4)})
    def test_large_weights(self): self.compare(cycle_counts(4), {i: (1 << 500) + i for i in range(4)})
    def test_disconnected(self): self.compare({0: {0: 1}, 1: {9: 1}, 2: {9: 1}, 3: {}})
    def test_no_mutation(self):
        a = {0: {0: 1, 1: 0}, 1: {0: 7}}; b = copy.deepcopy(a)
        self.compare(a); self.assertEqual(a, b)
    def test_seeded_weighted(self):
        rng = random.Random(4312)
        for _ in range(80):
            a = {r: {c: v for c in range(5) if (v := rng.randrange(3))} for r in range(4)}
            w = {r: rng.randrange(7) for r in a}
            self.compare(a, w)
    def test_positive_pivots(self):
        for a in ({0: {0: 1, 1: 2}, 1: {0: 1, 1: 1}}, cactus_counts(2)):
            p = self.compare(a)
            self.assertEqual(p['matched_weight'], arbitrary_positive_optimum(a))
    def test_zero_budget_refusal(self):
        self.assertEqual(optimize_counts({0: {0: 1}}, limits=Limits(max_work=0))['status'], 'RESOURCE_LIMIT')
    def test_rank_budget_refusal(self):
        p = optimize_counts(cycle_counts(3), prepeel=False, limits=Limits(max_block_rank=0))
        self.assertEqual(p['status'], 'RESOURCE_LIMIT')
    def test_cancellation_callback(self):
        class Stop(Exception): pass
        def stop(): raise Stop
        with self.assertRaises(Stop): optimize_counts({0: {0: 1}}, check=stop)
    def test_reject_bool_count(self):
        with self.assertRaises(ValueError): optimize_counts({0: {0: True}})
    def test_reject_negative_count(self):
        with self.assertRaises(ValueError): optimize_counts({0: {0: -1}})
    def test_reject_missing_weight(self):
        with self.assertRaises(ValueError): optimize_counts({0: {}}, {})
    def test_reject_nonunit_allowed(self):
        with self.assertRaises(ValueError): optimize_counts({0: {0: 2}}, allowed={(0, 0)})
    def test_forged_schedule(self):
        a = cycle_counts(3); p = optimize_counts(a)
        p['cancellations'].append([p['remaining_rows'][0], 0])
        self.assertFalse(verify_plan(a, p))
    def test_forged_score(self):
        a = {0: {0: 1}}; p = optimize_counts(a); p['matched_weight'] += 1
        self.assertFalse(verify_plan(a, p))
    def test_long_cycle_iterative(self):
        p = optimize_counts(cycle_counts(3000), prepeel=False)
        self.assertEqual(p['matched_weight'], 2999)
        self.assertEqual(p['stats']['max_block_rank'], 1)


class PowerTests(unittest.TestCase):
    def test_literal_paths(self):
        for n in range(1, 10):
            for row in (False, True):
                for eligibility in ((True, True), (True, False), (False, True), (False, False)):
                    result = periodic_path_table(n, first_is_row=row, eligibility=eligibility,
                        weight=3, potentials=((1, 4), (2, 5)), certificate=True)
                    got = {(x['first'], x['last'], x['direction']): x['score'] for x in result['table']}
                    self.assertEqual(got, path_oracle(n, 3, row, eligibility, ((1, 4), (2, 5))))
                    self.assertTrue(verify_power_certificate(result['certificate']))
    def test_small_cycles(self):
        for n in range(2, 15):
            p = periodic_cycle_optimum(n, weight=7)
            self.assertEqual(p['matched_weight'], (n-1)*7)
    def test_huge_binary_cycle(self):
        n = 1 << 1024
        p = periodic_cycle_optimum(n, certificate=True)
        self.assertEqual(p['matched_weight'], n-1)
        self.assertEqual(p['deferred_weight'], 1)
        self.assertTrue(verify_power_certificate(p['certificate']))
        self.assertLess(p['matrix_products'], 3*n.bit_length())
    def test_forged_matrix(self):
        p = periodic_path_table(99, certificate=True)['certificate']
        p['nodes'][-1]['matrix'][0][0] = 999999
        self.assertFalse(verify_power_certificate(p))
    def test_forged_exponent(self):
        p = periodic_path_table(99, certificate=True)['certificate']
        p['parameters']['length'] = 97
        self.assertFalse(verify_power_certificate(p))
    def test_forged_reference(self):
        p = periodic_path_table(99, certificate=True)['certificate']
        p['nodes'][-1]['left'] = len(p['nodes'])
        self.assertFalse(verify_power_certificate(p))
    def test_forged_word(self):
        p = periodic_path_table(99, certificate=True)['certificate']
        p['nodes'][3]['right'] = 1
        self.assertFalse(verify_power_certificate(p))
    def test_bool_matrix(self):
        p = periodic_path_table(9, certificate=True)['certificate']; p['nodes'][0]['matrix'][0][0] = False
        self.assertFalse(verify_power_certificate(p))
    def test_bad_parameters(self):
        with self.assertRaises(ValueError): periodic_path_table(0)
        with self.assertRaises(ValueError): periodic_cycle_optimum(1)
        with self.assertRaises(ValueError): periodic_path_table(10, potentials=((4, 1), (0, 0)))


class TransportTests(unittest.TestCase):
    def test_literal_transport(self):
        a = {0: {0: 1, 1: 2}, 1: {0: 1, 1: 1}}
        p = optimize_counts(a, {0: 5, 1: 1})
        c = transport_circuit(a, p, {0: 5, 1: 1})
        self.assertEqual(expand_circuit(c), literal_transport(a, p['cancellations']))
    def test_random_observables(self):
        rng = random.Random(809)
        for _ in range(80):
            a = {r: {c: v for c in range(5) if (v := rng.randrange(3))} for r in range(5)}
            p = optimize_counts(a, limits=Limits(max_block_rank=None))
            cir = transport_circuit(a, p)
            literal = literal_transport(a, p['cancellations'])
            self.assertEqual(expand_circuit(cir), literal)
            z = {c: rng.randrange(-5, 6) for c in range(5)}
            self.assertEqual(evaluate_circuit(cir, z),
                             {r: sum(v*z[c] for c, v in row.items()) for r, row in literal.items()})
    def test_zero_residual_rows_preserved(self):
        a = {0: {0: 1}, 1: {0: 1}}
        p = optimize_counts(a); c = transport_circuit(a, p)
        self.assertEqual(len(expand_circuit(c)), 1)
        self.assertEqual(list(expand_circuit(c).values()), [{}])
    def test_dense_residual(self):
        a = {0: {0: 1, **{j: 2 for j in range(1, 21)}}}
        a.update({r: {0: 1} for r in range(1, 21)})
        w = {r: (100 if r == 0 else 1) for r in a}
        p = optimize_counts(a, w); c = transport_circuit(a, p, w)
        self.assertEqual(p['cancelled_rows'], [0])
        self.assertEqual(sum(len(row) for row in expand_circuit(c).values()), 400)
        self.assertEqual(set(evaluate_circuit(c, dict.fromkeys(range(1, 21), 1)).values()), {40})
    def test_expansion_guard(self):
        a = {0: {0: 1, 1: 2}, 1: {0: 1}}; w = {0: 5, 1: 1}
        c = transport_circuit(a, optimize_counts(a, w), w)
        with self.assertRaises(ValueError): expand_circuit(c, max_output_entries=0)
    def test_bad_circuit_reference(self):
        a = {0: {0: 1}}; c = transport_circuit(a, optimize_counts(a))
        c['nodes'][0]['later'] = [[0, 1]]
        with self.assertRaises(ValueError): evaluate_circuit(c, {})
    def test_triangle_deferred_forest(self):
        edges = {0: (0,1), 1: (1,2), 2: (2,0)}
        a = {0: {0:1, 1:1, 2:1}}
        p = optimize_counts(a); f = deferred_forest(3, edges, a, p)
        self.assertEqual(len(f['forest']), 2)
        self.assertFalse(set(f['forest']) & set(f['pivot_edges']))
    def test_all_forests_partial(self):
        edges = {0:(0,1), 1:(1,2), 2:(2,0), 3:(0,3), 4:(3,2), 5:(1,3)}
        a = {0:{0:1,1:1,2:1}, 1:{2:1,3:1,4:1}, 2:{0:1,5:1,3:1}, 3:{1:1,4:1,5:1}}
        w = {0:8, 1:1, 2:7, 3:3}; p = optimize_counts(a,w)
        values = [brute_private({r:{c:v for c,v in row.items() if c not in f}
                                 for r,row in a.items()},w) for f in spanning_forests(4,edges)]
        self.assertEqual(p['matched_weight'], max(values))
        f = deferred_forest(4,edges,a,p,weights=w)
        self.assertEqual(len(f['forest']),3)
    def test_uncapped_parity(self):
        edges = {0:(0,1),1:(0,1)}; a = {0:{0:1,1:3}}
        p = optimize_counts(a)
        self.assertEqual(len(deferred_forest(2,edges,a,p)['forest']),1)
        capped = {0:{0:1,1:2}}
        with self.assertRaises(ValueError): deferred_forest(2,edges,capped,optimize_counts(capped))
    def test_forced_forest(self):
        edges = {0:(0,1),1:(1,2),2:(2,0)}; a = {0:{0:1,1:1,2:1}}
        p = optimize_counts(a, allowed={(0,0)})
        f = deferred_forest(3,edges,a,p,forced_forest=[1],allowed={(0,0)})
        self.assertIn(1,f['forest'])
        with self.assertRaises(ValueError): deferred_forest(3,edges,a,p,forced_forest=[0],allowed={(0,0)})

if __name__ == '__main__': unittest.main()
