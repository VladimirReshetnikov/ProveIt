"""Lower-forest optimization, source-bound kernel replay and shared discovery."""
from contextlib import ExitStack
from copy import deepcopy
from itertools import combinations
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.core_handlebody import _chosen_forest, select_core_forest
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from tests.test_core_three_handles import BANK, EXTRA, geometry
from tests.test_moment_cut_handlebodies import operations

NEW = ('pilot/fibonacci_lst_04/0', 'pilot/fibonacci_lst_06/0',
       'pilot/fibonacci_lst_08/0', 'pilot/fibonacci_lst_10/0',
       'pilot/lst_4_9/0', 'pilot/finite_trefoil/0')


def components(n, edges, chosen):
    groups = [{i} for i in range(n)]
    acyclic = True
    for e in chosen:
        a, b = edges[e]
        x = next(g for g in groups if a in g); y = next(g for g in groups if b in g)
        if x is y: acyclic = False
        else: x.update(y); groups.remove(y)
    return acyclic, {frozenset(g) for g in groups}


class LowerForestTests(unittest.TestCase):
    def test_200_graph_optima_against_exhaustive_spanning_forests(self):
        rng = random.Random(261012105)
        for _ in range(200):
            n = rng.randrange(1, 7)
            edges = [[rng.randrange(n), rng.randrange(n)] for _ in range(rng.randrange(10))]
            costs = [rng.randrange(5) for e in edges]
            core = dict(handles0=[dict(id=i) for i in range(n)],
                        handles1=[dict(id=i, ends=e) for i,e in enumerate(edges)],
                        handles2=[dict(id=0, cycle=[dict(dimension=1, handle=i)
                                                  for i,c in enumerate(costs) for _ in range(c)])])
            target = components(n, edges, range(len(edges)))[1]
            size = n-len(target)
            best = max(sum(costs[e] for e in chosen) for chosen in combinations(range(len(edges)),size)
                       if components(n,edges,chosen)==(True,target))
            tree = select_core_forest(core)
            self.assertEqual(sum(costs[e] for e in tree), best)
            self.assertEqual(components(n,edges,tree),(True,target))
            checked, roots = _chosen_forest(core,tree,lambda:None)
            self.assertEqual(checked,tree)
            self.assertEqual(roots,[min(g) for v in range(n) for g in target if v in g])

    def test_six_new_sources_both_boundary_methods(self):
        old = json.loads((Path(__file__).parents[2]/'synthesis/data/weighted-forest-audit.json').read_text())
        references = {r['id']:r['regina']['histogram'] for r in old['cases'] if r['id'] in NEW}
        for c in [c for c in BANK if c['id'] in NEW]:
            args = c['triangulation'],c['coordinates']
            # This assertion records the original fixed-forest geometric refusal.
            # The default signed-group fallback can now certify some such cuts.
            self.assertEqual(normal_cut_handlebodies(*args,lower_forest='source',
                group_fallback=False)['status'],'INCONCLUSIVE')
            for method in ('masks','moments'):
                r = normal_cut_handlebodies(*args,boundary_method=method,record_certificate=True)
                self.assertEqual(r['status'],'COMPLETE')
                self.assertEqual(r['census']['histogram'],references[c['id']])
                self.assertEqual(len(r['stats']['lower_forest_attempts']),2)
                self.assertTrue(verify_normal_cut_handlebodies(*args,r['certificate']))
                explicit = normal_cut_handlebodies(*args,boundary_method=method,lower_forest='max_passages',record_certificate=True)
                self.assertEqual(explicit['certificate'],r['certificate'])
                if c['id'] in NEW[2:4]:
                    self.assertEqual(r['certificate']['kernel']['schema'],'bundle-boundary-kernel-v3')

    def test_late_retry_shares_source_boundary_and_budgets(self):
        c = next(c for c in BANK if c['id']==NEW[2]); args=c['triangulation'],c['coordinates']
        with patch('fastunknot.normal_cut_handlebodies.normal_cut_parallelity',wraps=normal_cut_parallelity) as source:
            with patch('fastunknot.normal_cut_handlebodies.normal_parallelity_boundary_words',wraps=normal_parallelity_boundary_words) as boundary:
                r=normal_cut_handlebodies(*args,precheck_core=False,record_certificate=True)
                self.assertEqual(source.call_count,1);self.assertEqual(boundary.call_count,1)
                self.assertEqual(len(r['stats']['lower_forest_attempts']),2)
        self.assertEqual(r['status'],'COMPLETE')
        r=normal_cut_handlebodies(*args,precheck_core=False,boundary_method='moments',record_certificate=True)
        cycles=sum(s['orbit_cycles'] for s in r['stats']['parallelity'].values())+r['stats']['boundary']['census']['orbit_cycles']
        exact=normal_cut_handlebodies(*args,precheck_core=False,boundary_method='moments',max_cycles=cycles,record_certificate=True)
        self.assertEqual(exact['certificate'],r['certificate'])
        for limit in (0,cycles-1):
            limited=normal_cut_handlebodies(*args,precheck_core=False,boundary_method='moments',max_cycles=limit,record_certificate=True)
            self.assertEqual(limited['status'],'INCONCLUSIVE');self.assertNotIn('certificate',limited)
        count=operations(r['certificate'])
        self.assertTrue(verify_normal_cut_handlebodies(*args,r['certificate'],max_operations=count))
        self.assertFalse(verify_normal_cut_handlebodies(*args,r['certificate'],max_operations=count-1))

    def test_kernel_forest_hostility_and_independent_replay(self):
        c=next(c for c in BANK if c['id']==NEW[2]);args=c['triangulation'],c['coordinates']
        p=normal_cut_handlebodies(*args,record_certificate=True)['certificate']
        names=('fastunknot.core_handlebody.select_core_forest','fastunknot.core_handlebody._chosen_forest',
               'fastunknot.core_handlebody._forest','fastunknot.bundle_boundary_kernel._chosen_forest',
               'fastunknot.bundle_boundary_kernel.bundle_boundary_kernel')
        with ExitStack() as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(*args,p))
        for mutate in (lambda k:k['forest'].pop(),lambda k:k['forest'].append(k['forest'][0]),
                       lambda k:k['forest'].__setitem__(0,True),lambda k:k['forest'].__setitem__(0,-1),
                       lambda k:k['forest'].__setitem__(0,'0xgarbage'),lambda k:k.update(forest=None),
                       lambda k:k.update(schema='bundle-boundary-kernel-v2'),lambda k:k.update(extra=1)):
            bad=deepcopy(p);mutate(bad['kernel']);self.assertFalse(verify_normal_cut_handlebodies(*args,bad))
        encoded=deepcopy(p);encoded['kernel']['forest']=[hex(e) for e in p['kernel']['forest']]
        self.assertTrue(verify_normal_cut_handlebodies(*args,encoded))

    def test_fixed_lower_forest_in_top_and_kernel_consumers(self):
        c=next(c for c in BANK if c['id']=='interior_1_2/mixed')
        g=geometry(c);tree=select_core_forest(g['core'])
        r=normal_cut_handlebodies(c['triangulation'],c['coordinates'],lower_forest='max_passages',record_certificate=True)
        self.assertEqual(r['status'],'COMPLETE')
        self.assertEqual(r['certificate']['kernel']['forest'],tree)
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],r['certificate']))

    def test_old_success_proofs_preserved_and_recordless_alternative(self):
        for c in [BANK[0],next(c for c in BANK if c['id']=='interior_1_2/mixed'),EXTRA[0]]:
            args=c['triangulation'],c['coordinates']
            old=normal_cut_handlebodies(*args,lower_forest='source',record_certificate=True)
            adaptive=normal_cut_handlebodies(*args,record_certificate=True)
            self.assertEqual(old['certificate'],adaptive['certificate'])
        c=next(c for c in BANK if c['id']==NEW[0]);args=c['triangulation'],c['coordinates']
        plain=normal_cut_handlebodies(*args);proof=normal_cut_handlebodies(*args,record_certificate=True)
        self.assertEqual(plain['census'],proof['census']);self.assertNotIn('certificate',plain)

    def test_invalid_forests_modes_and_interruption(self):
        c=EXTRA[0];g=geometry(c);tree=select_core_forest(g['core'])
        for bad in (True,{},[True],[-1],tree[:-1],tree+[tree[0]]):
            with self.assertRaises(ValueError):_chosen_forest(g['core'],bad,lambda:None)
        for bad in (None,True,[],{},'largest'):
            with self.assertRaises(ValueError):select_core_forest(g['core'],strategy=bad)
            with self.assertRaises(ValueError):normal_cut_handlebodies(c['triangulation'],c['coordinates'],lower_forest=bad)
        class Stop:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):select_core_forest(g['core'],check=Stop())
        with self.assertRaisesRegex(RuntimeError,'cancelled'):normal_cut_handlebodies(c['triangulation'],c['coordinates'],check=Stop())


if __name__=='__main__':unittest.main()
