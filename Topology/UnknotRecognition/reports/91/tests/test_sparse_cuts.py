import copy
import json
import random
import unittest
from itertools import combinations
from sparse_cuts import (solve, validate, InputError, BudgetExceeded, connected_support_bound,
                         support_bound, circular_ladder, thue_morse, witness_dag, cut_addresses,
                         mark_address, append_power)
from checker import (verify_certificate, verify_witness, verify_addresses, leaf_complete,
                     metadata as independent_metadata)
from reference import expand, brute_signature, expanded_small_cut_signature


def grammar(leaf):
    return {"schema": "proveit.graph-grammar.v1", "nodes": [leaf]}


def leaf(n, edges, terminals=None):
    node = {"kind": "leaf", "vertices": n,
            "edges": [list(e) if len(e) == 3 else [*e, 1] for e in edges],
            "terminals": list(range(n)) if terminals is None else list(terminals)}
    named = set(node["terminals"]) | {v for e in node["edges"] for v in e[:2]}
    isolated = sorted(set(range(n))-named)
    if isolated and n > 1: node["isolated_vertices"] = isolated
    return node


def star_pair(arms):
    a = leaf(arms+1, [(0, v) for v in range(1, arms+1)])
    join = {"kind": "join", "left": 0, "right": 0,
            "left_map": list(range(arms+1)),
            "right_map": [0]+list(range(arms+1, 2*arms+1)),
            "terminals": list(range(2*arms+1))}
    return {"schema": "proveit.graph-grammar.v1", "nodes": [a, join]}


class TestSparseCuts(unittest.TestCase):
    def compare(self, g, k=3, replay=True):
        r = solve(g, k)
        self.assertEqual(r.response(), brute_signature(expand(g, 16, 100), k))
        self.assertEqual([m.record() for m in r.metadata], independent_metadata(g))
        if replay:
            self.assertTrue(verify_certificate(g, r.certificate())["verified"])
        return r

    def test_single_vertex(self):
        self.compare(grammar(leaf(1, [])))

    def test_private_single_vertex(self):
        self.assertEqual(self.compare(grammar(leaf(1, [], []))).response(), {(0,0): 0})

    def test_one_edge_all_exact_flags(self):
        r = self.compare(grammar(leaf(2, [(0,1)], [])))
        self.assertEqual(r.response(), {(0,1):0, (0,2):0, (0,0):1})

    def test_loop_marks(self):
        r = self.compare(grammar(leaf(2, [(0,0),(1,1),(0,1)], [])))
        self.assertEqual(r.response()[(0,3)], 1)

    def test_parallel_edges(self):
        self.compare(grammar(leaf(2, [(0,1)]*4)))

    def test_binary_weight(self):
        self.compare(grammar(leaf(3, [(0,1,1<<4096),(1,2,1)])))

    def test_k4_vs_prism(self):
        k4 = grammar(leaf(4, list(combinations(range(4),2)), []))
        self.assertNotIn((0,3), self.compare(k4).response())
        self.assertEqual(self.compare(circular_ladder(3)).response()[(0,3)],3)

    def test_ladders_all_small(self):
        for n in range(1,8):
            self.compare(circular_ladder(n))

    def test_thresholds(self):
        for k in range(5):
            self.compare(circular_ladder(3), k)

    def test_loop_forming_quotient(self):
        g = grammar(leaf(2,[(0,1)]))
        g["nodes"].append({"kind":"map","child":0,"mapping":[0,0],"terminals":[]})
        self.compare(g)

    def test_forget_and_permute(self):
        g = grammar(leaf(4,[(0,1),(1,2),(2,3)]))
        g["nodes"].append({"kind":"map","child":0,"mapping":[2,0,1,3],"terminals":[3,2]})
        self.compare(g)

    def test_self_identification_inside_join(self):
        g = grammar(leaf(3,[(0,1),(1,2)]))
        g["nodes"].append({"kind":"join","left":0,"right":0,
                          "left_map":[0,1,0],"right_map":[1,2,2],"terminals":[2,0]})
        self.compare(g)

    def test_disjoint_join(self):
        g = grammar(leaf(2,[(0,1)]))
        g["nodes"].append({"kind":"join","left":0,"right":0,
                          "left_map":[0,1],"right_map":[2,3],"terminals":[]})
        self.assertEqual(self.compare(g).response()[(0,3)],0)

    def test_many_unseen_components(self):
        g = grammar(leaf(7,[(0,1),(2,3),(4,5)], [0]))
        self.compare(g)

    def test_exponential_terminal_components(self):
        r = solve(grammar(leaf(10,[])), 0)
        self.assertEqual(len(r.response()),1024)
        self.assertEqual(r.metadata[0].terminal_components,10)

    def test_binary_hidden_component_count(self):
        g = grammar(leaf(2,[(0,1)],[]))
        for i in range(128):
            g["nodes"].append({"kind":"join","left":i,"right":i,"left_map":[],"right_map":[],"terminals":[]})
        r = solve(g)
        self.assertEqual(r.metadata[-1].hidden,1<<128)
        self.assertLessEqual(max(map(len,r.tables)),4)
        self.assertTrue(verify_certificate(g,r.certificate())["verified"])
        w = witness_dag(r)
        self.assertTrue(verify_addresses(g,w,cut_addresses(r),[mark_address(r,c) for c in (0,1)])["verified"])

    def test_huge_connected_power(self):
        g = circular_ladder(1<<256)
        r = solve(g)
        self.assertEqual(r.metadata[-1].vertices,1<<257)
        self.assertTrue(r.metadata[-1].interior_cubic)
        self.assertFalse(r.has_marked_cut())
        self.assertTrue(verify_certificate(g,r.certificate())["verified"])
        with self.assertRaises(ValueError):
            expand(g)

    def test_nested_nonuniform_grammar(self):
        for d in range(2):
            self.compare(thue_morse(d))
        g=thue_morse(128); r=solve(g)
        self.assertTrue(r.has_marked_cut())
        self.assertTrue(r.metadata[-1].interior_cubic)
        self.assertTrue(verify_certificate(g,r.certificate())["verified"])
        self.assertTrue(verify_witness(g,witness_dag(r))["verified"])

    def test_edge_addresses(self):
        for g in [circular_ladder(1),circular_ladder(2),circular_ladder(3),thue_morse(30)]:
            r=solve(g); w=witness_dag(r)
            self.assertTrue(verify_addresses(g,w,cut_addresses(r),[mark_address(r,c) for c in (0,1)])["verified"])

    def test_budget_index_changes_no_answers(self):
        for a in range(1,9):
            g=star_pair(a)
            fast,slow=solve(g),solve(g,cost_indexed=False)
            self.assertEqual(fast.response(),slow.response())
            self.assertLessEqual(fast.operations,slow.operations)

    def test_complete_certificate_roundtrip(self):
        g=circular_ladder(3)
        self.assertTrue(verify_certificate(g,json.loads(json.dumps(solve(g).certificate())))["verified"])

    def test_deleted_record_rejected(self):
        g=circular_ladder(3); cert=solve(g).certificate(); cert["tables"][-1].pop()
        with self.assertRaises(ValueError): verify_certificate(g,cert)

    def test_forged_cost_rejected(self):
        g=circular_ladder(3); cert=solve(g).certificate()
        for row in cert["tables"][-1]:
            if row[1]==3: row[2]=0
        with self.assertRaises(ValueError): verify_certificate(g,cert)

    def test_forged_leaf_witness_rejected(self):
        g=circular_ladder(3); cert=solve(g).certificate(); cert["tables"][0][0][3]^=1
        with self.assertRaises(ValueError): verify_certificate(g,cert)

    def test_source_change_rejected(self):
        g=circular_ladder(3); cert=solve(g).certificate(); g["nodes"][0]["edges"][0][2]=2
        with self.assertRaises(ValueError): verify_certificate(g,cert)

    def test_forged_metadata_rejected(self):
        g=circular_ladder(3); cert=solve(g).certificate(); cert["metadata"][-1]["hidden_components_hex"]="0x2"
        with self.assertRaises(ValueError): verify_certificate(g,cert)

    def test_bad_witness_address_rejected(self):
        g=circular_ladder(3); r=solve(g); cuts=cut_addresses(r); cuts.append(copy.deepcopy(cuts[0]))
        with self.assertRaises(ValueError): verify_addresses(g,witness_dag(r),cuts,[mark_address(r,c) for c in (0,1)])

    def test_invalid_zero_negative_and_boolean_weights(self):
        for w in [0,-1,True,1.0]:
            with self.assertRaises(InputError): solve(grammar(leaf(2,[(0,1,w)])))

    def test_invalid_interfaces_and_cycles(self):
        for mapping in [[0,2],[0],[True,1]]:
            g=grammar(leaf(2,[(0,1)]))
            g["nodes"].append({"kind":"map","child":0,"mapping":mapping,"terminals":[]})
            with self.assertRaises(InputError): solve(g)
        g=grammar(leaf(2,[(0,1)]));g["nodes"].append({"kind":"map","child":1,"mapping":[0,1],"terminals":[]})
        with self.assertRaises(InputError): solve(g)

    def test_budget_exhaustion_is_inconclusive(self):
        with self.assertRaises(BudgetExceeded): solve(circular_ladder(32),operation_limit=10)
        with self.assertRaises(BudgetExceeded): solve(grammar(leaf(12,[])),0,state_limit=100)

    def test_no_false_cubic_claim(self):
        r=self.compare(grammar(leaf(3,[(0,1),(1,2)],[])))
        self.assertFalse(r.metadata[-1].interior_cubic)

    def test_random_weighted_leaves(self):
        rng=random.Random(84112)
        for _ in range(150):
            n=rng.randrange(1,8)
            edges=[(rng.randrange(n),rng.randrange(n),rng.randrange(1,5)) for _ in range(rng.randrange(12))]
            terms=rng.sample(range(n),rng.randrange(n+1))
            self.compare(grammar(leaf(n,edges,terms)),rng.randrange(4))

    def test_direct_expanded_cut_enumerator(self):
        for n in range(1,8):
            graph=expand(circular_ladder(n))
            self.assertEqual(expanded_small_cut_signature(graph,3),brute_signature(graph,3))

    def test_connected_bound_examples(self):
        for r in range(1,10):
            g=grammar(leaf(r+1,[(0,i) for i in range(1,r+1)],range(1,r+1)))
            result=solve(g)
            colors={a for a,b in result.response()}
            self.assertLessEqual(len(colors),connected_support_bound(r,3))

    def test_implicit_leaf_expansion_rejected(self):
        node={"kind":"leaf","vertices":1<<128,"edges":[],"terminals":[]}
        with self.assertRaises(InputError): solve(grammar(node))
        with self.assertRaises(ValueError): verify_certificate(grammar(node),solve(grammar(leaf(1,[]))).certificate())
        self.compare(grammar(leaf(5,[],[])))

    def test_address_role_confusion_rejected(self):
        g=circular_ladder(3);r=solve(g);cuts=cut_addresses(r)
        cuts[0]["color"]=0
        with self.assertRaises(ValueError):
            verify_addresses(g,witness_dag(r),cuts,[mark_address(r,c) for c in (0,1)])

    def test_power_zero_rejected(self):
        with self.assertRaises(InputError): append_power([],0,0,1)

if __name__ == "__main__":
    unittest.main()
