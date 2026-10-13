"""Exact covering existence without an eagerly materialized region family."""
from itertools import combinations
import unittest
from unittest.mock import patch

from fastunknot.normal_cocycle import CocycleLimit
from fastunknot import Diagram
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.pachner_cover_oracle import _CoverOracle
from fastunknot.pachner_cover_search import search_pachner_cover,find_pachner_descent
from fastunknot.pachner_cover_verify import verify_pachner_cover,inspect_pachner_descent
from commitment_research.fixtures import independent_bipyramids,endpoint_keys
from causal_research.fixtures import descent_gadgets


def components(graph,selected):
    pending=set(selected);count=0
    while pending:
        count+=1;todo=[pending.pop()]
        while todo:
            reached=set(graph[todo.pop()])&pending
            pending-=reached;todo.extend(reached)
    return count


def stats():return dict(oracle_queries=0,oracle_cache_hits=0,oracle_states=0)


class CoverOracleTests(unittest.TestCase):
    def test_every_small_footprint_agrees_with_literal_cover_existence(self):
        graphs=([set(),set()], [{1},{0,2},{1,3},{2}],
            [{1,2},{0,3},{0,3},{1,2}], [{1},{0,2},{1,3,4},{2},{2},set()])
        comparisons=0
        for graph in graphs:
            subsets=[frozenset(s)for size in range(len(graph)+1)for s in combinations(range(len(graph)),size)]
            for maximum in range(len(graph)+1):
                for limit in range(3):
                    covers=[s for s in subsets if len(s)<=maximum and components(graph,s)<=limit]
                    oracle=_CoverOracle(graph,maximum,limit);record=stats()
                    for footprint in subsets:
                        witness=oracle.complete(footprint,record,lambda:None)
                        self.assertEqual(witness is not None,any(footprint<=s for s in covers))
                        if witness is not None:
                            self.assertTrue(footprint<=set(witness));self.assertLessEqual(len(witness),maximum)
                            self.assertLessEqual(components(graph,witness),limit)
                        self.assertEqual(oracle.complete(footprint,record,lambda:None),witness)
                        comparisons+=1
        self.assertGreater(comparisons,1000)

    def test_first_witness_does_not_restrict_later_cover_choices(self):
        graph=({1},{0,2},{1,3},{2});oracle=_CoverOracle(graph,3,1);record=stats()
        first=oracle.extend(None,frozenset({0}),record,lambda:None)
        self.assertEqual(first.region,(0,))
        later=oracle.extend(first,frozenset({2}),record,lambda:None)
        self.assertEqual(later.consumed,frozenset({0,2}));self.assertEqual(later.region,(0,1,2))
        self.assertFalse(oracle.extend(later,frozenset({3}),record,lambda:None))
        self.assertFalse(oracle.extend(False,frozenset({1}),record,lambda:None))

    def test_cap_and_interruption_cannot_cache_a_false_exclusion(self):
        oracle=_CoverOracle(({1},{0,2},{1}),3,1,max_states=0);record=stats()
        footprint=frozenset({0,2})
        with self.assertRaises(CocycleLimit):oracle.complete(footprint,record,lambda:None)
        self.assertNotIn(footprint,oracle.cache)
        oracle.max_states=None
        self.assertEqual(oracle.complete(footprint,record,lambda:None),(0,1,2))
        fresh=_CoverOracle(({1},{0,2},{1}),3,1)
        def stop():raise InterruptedError('completion interrupted')
        with self.assertRaises(InterruptedError):fresh.complete(footprint,stats(),stop)
        self.assertNotIn(footprint,fresh.cache)

    def test_native_oracle_and_indexed_languages_and_replay_agree(self):
        fixture=independent_bipyramids(2);raw=fixture['triangulation'];h=fixture['heights']
        for radius,limit in ((3,1),(4,2),(6,1)):
            options=dict(max_region_size=radius,max_components=limit,max_upward=0,
                max_nodes=None,collect_endpoints=True)
            indexed=search_pachner_cover(raw,h,cover_backend='indexed',**options)
            oracle=search_pachner_cover(raw,h,cover_backend='oracle',**options)
            self.assertEqual(indexed['status'],oracle['status'])
            self.assertEqual(endpoint_keys(raw,h,indexed['endpoints']),endpoint_keys(raw,h,oracle['endpoints']))
            self.assertEqual(indexed['stats']['nodes'],oracle['stats']['nodes'])
            self.assertEqual(oracle['stats']['regions_indexed'],0)
            for proof in oracle['endpoints']:
                self.assertTrue(verify_pachner_cover(raw,h,proof,max_region_size=radius,max_components=limit,max_upward=0))

    def test_first_descent_never_builds_the_unused_ambient_index(self):
        fixture=descent_gadgets(1);raw=fixture['triangulation'];h=fixture['heights']
        with patch('fastunknot.pachner_cover_search._build_index',side_effect=AssertionError('eager index')):
            answer=find_pachner_descent(raw,h,max_upward=1,max_nodes=None)
        self.assertEqual(answer['status'],'DESCENT_FOUND')
        self.assertEqual(answer['stats']['cover_backend'],'oracle')
        self.assertTrue(inspect_pachner_descent(raw,h,answer['certificate'],max_upward=1))

    def test_explicit_index_caps_keep_their_previous_meaning(self):
        fixture=independent_bipyramids(1);raw=fixture['triangulation'];h=fixture['heights']
        self.assertEqual(search_pachner_cover(raw,h,max_region_size=3,max_regions=0)['status'],'INCONCLUSIVE')
        for options in ({'cover_backend':'wrong'},{'cover_backend':'oracle','max_regions':1},
                        {'max_oracle_states':False}):
            with self.assertRaises(ValueError):search_pachner_cover(raw,h,max_region_size=3,**options)

    def test_actual_diagram_advances_before_spending_the_node_allowance(self):
        d=Diagram.from_braid(2,[1,1,1])
        with patch('fastunknot.pachner_cover_search._build_index',side_effect=AssertionError('ambient index')):
            answer=pachner_seed_decide(d,max_upward=1,max_region_size=6,max_nodes=5,
                max_work=2000000,shellings=True,optimize=True)
        self.assertEqual(answer['status'],'INCONCLUSIVE')
        self.assertEqual(answer['stats']['root_probe']['nodes'],1)
        self.assertEqual(answer['stats']['search']['nodes'],4)
        self.assertEqual(answer['stats']['search']['moves'],3)
        self.assertEqual(answer['stats']['search']['regions_indexed'],0)
        self.assertNotIn('certificate',answer)


if __name__=='__main__':unittest.main()
