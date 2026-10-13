"""Lazy preparation keeps finite priority, exact source proofs and complete replay."""
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_braid import recognize, verify
from fastunknot.compressed_braid import forest
from compressed_braid_research.families import sleeve, singleton_forest
from compressed_braid_research.exceptional import grammar, join


class LazyForestTests(unittest.TestCase):
    def test_only_obstructing_factor_is_projected_in_production_and_replay(self):
        data = join(singleton_forest(12, 32), grammar(2, [1, 1, 1]))
        original, calls = forest.project, []
        def selected(source, low, high, **kwargs):
            calls.append((low, high))
            self.assertEqual((low, high), (37, 38))
            return original(source, low, high, **kwargs)
        with patch.object(forest, 'project', selected):
            result = recognize(data, max_nodes=0, fallback_max_generators=0)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(result['factor_order'], [12])
        self.assertEqual(calls, [(37, 38), (37, 38)])
        self.assertEqual(verify(data, result['certificate']), 'KNOTTED')

    def test_positive_forests_need_all_factors_and_identical_complete_proofs(self):
        for factors in (1, 3, 8):
            data = singleton_forest(factors, 4)
            current, old = recognize(data), recognize(data, use_lazy_factors=False)
            self.assertEqual(current['status'], 'UNKNOT')
            self.assertEqual(current['certificate'], old['certificate'])
            if factors > 1:
                self.assertEqual(sorted(current['factor_order']), list(range(factors)))
            self.assertEqual(verify(data, current['certificate']), 'UNKNOT')

    def test_plan_metadata_and_rule_bound_against_every_actual_projection(self):
        rng = random.Random(261008500)
        cases = [singleton_forest(n, 5, negative_index=n-1) for n in range(2, 8)]
        # Nonconvex child support: {factor 0, factor 2} has a hull covering
        # factor 1, so intersecting hulls is a bound rather than an exact count.
        mixed = dict(strands=6, rules=[['e'], ['g',1], ['g',5], ['c',1,2],
                                      ['g',3], ['c',3,4]], root=5)
        root = 5
        for _ in range(32):
            mixed['rules'].append(['c', root, root]); root=len(mixed['rules'])-1
        mixed['rules'].append(['c',root,5]); root=len(mixed['rules'])-1
        for letter in (2,4):
            mixed['rules'].append(['g',letter]); node=len(mixed['rules'])-1
            mixed['rules'].append(['c',root,node]); root=len(mixed['rules'])-1
        mixed['root']=root
        cases.append(mixed)
        for _ in range(100):
            data = grammar(2, [1, -1, 1])
            for _ in range(rng.randrange(1, 6)):
                word = rng.choice(([1, 1, 1], [1, -1, 1], [-1, -1, -1]))
                data = join(data, grammar(2, word))
            # Dead and duplicate children must not contaminate root weights;
            # they still appear in the canonical projected grammar's size.
            node = len(data['rules']); data['rules'].append(['g', rng.randrange(1, data['strands'])])
            for _ in range(5):
                data['rules'].append(['c', node, node]); node = len(data['rules'])-1
            cases.append(data)
        for data in cases:
            s = forest.summarize(data)
            self.assertTrue(s['knot'])
            cuts = sorted(g for g, n in s['counts'].items() if n == 1)
            ends = [0] + cuts + [data['strands']]
            intervals = list(zip(ends, ends[1:]))
            for priority, bound, index, lo, hi, length, exponent in forest._factor_plan(data, s, intervals, lambda: None):
                projected = forest.project(data, lo+1, hi)
                actual = forest.summarize(projected)
                self.assertEqual((actual['length'], actual['exponent']), (length, exponent))
                self.assertGreaterEqual(bound, len(projected['rules']))
                m = projected['strands']
                self.assertEqual(priority, 0 if m <= 2 or abs(exponent)>m-1 else 1 if m==3 else 2)

    def test_duplicate_root_dependencies_propagate_full_weights(self):
        data = join(grammar(2, [1, 1, 1]), grammar(2, [-1, -1, -1]))
        # Build a new connected sum after a shared-node cube of a knot braid.
        root = data['root']; data['rules'].append(['c', root, root])
        data['rules'].append(['c', len(data['rules'])-1, root]); data['root']=len(data['rules'])-1
        data = join(data, grammar(2, [1, 1, 1]))
        s = forest.summarize(data); self.assertTrue(s['knot'])
        cuts = sorted(g for g,n in s['counts'].items() if n==1)
        ends = [0]+cuts+[data['strands']]
        plan = forest._factor_plan(data,s,list(zip(ends,ends[1:])),lambda:None)
        for _,_,_,lo,hi,length,exponent in plan:
            actual=forest.summarize(forest.project(data,lo+1,hi))
            self.assertEqual((length,exponent),(actual['length'],actual['exponent']))

    def test_disjoint_concatenations_do_not_distort_factor_cost(self):
        for negative in (0, 11):
            data = singleton_forest(12, 8, negative_index=negative)
            s = forest.summarize(data)
            ends = [0] + sorted(g for g,n in s['counts'].items() if n==1) + [data['strands']]
            plan = forest._factor_plan(data,s,list(zip(ends,ends[1:])),lambda:None)
            for _,bound,_,lo,hi,_,_ in plan:
                self.assertEqual(bound,len(forest.project(data,lo+1,hi)['rules']))
            result = recognize(data)
            self.assertEqual(result['factor_order'],[negative])
            self.assertEqual(result['status'],'KNOTTED')

    def test_links_are_checked_before_any_selected_negative_factor(self):
        data = join(grammar(2, [1, 1]), grammar(2, [1, 1, 1]))
        with patch.object(forest, '_factor_plan', side_effect=AssertionError), \
             patch.object(forest, 'project', side_effect=AssertionError):
            self.assertEqual(recognize(data)['status'], 'LINK')
        data = dict(strands=10**100, rules=[['e']], root=0)
        self.assertEqual(recognize(data)['status'], 'LINK')

    def test_single_strand_projection_is_exact_even_with_unreachable_rules(self):
        data = singleton_forest(4, 16)
        for strand in range(1, data['strands']+1):
            self.assertEqual(forest.project(data,strand,strand),
                             dict(strands=1,rules=[['e']],root=0))
        data = grammar(20,list(range(1,20)))
        result = recognize(data)
        self.assertEqual(result['status'],'UNKNOT')
        self.assertEqual(len(result['certificate']['leaves']),20)
        bad=deepcopy(data);bad['rules'].append(['g',True])
        with self.assertRaises(ValueError):recognize(bad)

    def test_replay_uses_no_planner_and_resource_failure_has_no_partial_proof(self):
        data = join(singleton_forest(8,16),grammar(2,[1,1,1]))
        full = recognize(data)
        with patch.object(forest,'_factor_plan',side_effect=AssertionError):
            self.assertEqual(verify(data,full['certificate']),'KNOTTED')
        self.assertEqual(recognize(data,max_work=full['resources']['work'])['status'],'KNOTTED')
        result = recognize(data,max_work=full['resources']['work']-1)
        self.assertEqual(result['status'],'INCONCLUSIVE')
        self.assertNotIn('certificate',result)
        with self.assertRaises(ValueError):recognize(data,use_lazy_factors=1)
        calls=0
        def cancel():
            nonlocal calls
            calls+=1
            if calls==10:raise ValueError('cancel planning')
        s=forest.summarize(data);cuts=sorted(g for g,n in s['counts'].items() if n==1)
        ends=[0]+cuts+[data['strands']]
        with self.assertRaisesRegex(ValueError,'cancel planning'):
            forest._factor_plan(data,s,list(zip(ends,ends[1:])),cancel)


if __name__=='__main__':unittest.main()
