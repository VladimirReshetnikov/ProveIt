"""Report 105's deferred forest theorem through current source consumers."""
from collections import Counter
from contextlib import ExitStack
from copy import deepcopy
from itertools import combinations
import random
import unittest
from unittest.mock import patch

from fastunknot.core_handlebody import (_deferred_forest, _occurrences,
    column_cancellation_plan, core_handlebody_certificate, select_core_forest)
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.bundle_boundary_kernel import bundle_boundary_kernel
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from tests.test_core_three_handles import BANK, EXTRA, geometry
from tests.test_lower_forests import components
from tests.test_moment_cut_handlebodies import operations


def abstract_core(n, edges, walks):
    # Synthetic closed walks exercise the finite theorem, not source validity.
    rows=[]
    for r,walk in enumerate(walks):
        cycle=[]
        for start in range(n):
            v=start;cycle=[]
            for e in walk:
                a,b=edges[e]
                if v not in (a,b):break
                cycle.extend([dict(dimension=0,handle=v),dict(dimension=1,handle=e)])
                v=b if v==a else a
            else:
                if v==start:break
        rows.append(dict(id=r,cycle=cycle))
    return dict(handles0=[dict(id=v) for v in range(n)],
        handles1=[dict(id=e,ends=list(ends)) for e,ends in enumerate(edges)],
        handles2=rows,handles3=[])



def literal_residual(walks, discarded):
    rows={r:Counter(e for e in walk if e not in discarded) for r,walk in enumerate(walks)}
    while rows:
        totals=Counter()
        for row in rows.values():totals.update(row)
        leaf=next((e for e,total in sorted(totals.items()) if total==1),None)
        if leaf is None:break
        r=next(r for r,row in rows.items() if row[leaf]);del rows[r]
    return set(rows)


class DeferredForestTests(unittest.TestCase):
    def test_all_forests_and_smallest_residual_on_closed_walks(self):
        rng=random.Random(261012111);examined=0
        for _ in range(160):
            n=rng.randrange(1,5);edges=[(v-1,v) for v in range(1,n)]
            edges += [(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(1,5))]
            adjacent=[[] for _ in range(n)]
            for e,(a,b) in enumerate(edges):adjacent[a].append((e,b));adjacent[b].append((e,a))
            walks=[]
            for _ in range(rng.randrange(0,5)):
                start=v=rng.randrange(n);walk=[]
                for _ in range(rng.randrange(1,6)):
                    e,v=rng.choice(adjacent[v]);walk.append(e)
                while v!=start:
                    w=v-1 if v>start else v+1;walk.append(max(v,w)-1);v=w
                walks.append(walk)
            core=abstract_core(n,edges,walks)
            plan=column_cancellation_plan(_occurrences(core,(),lambda:None))
            tree,_=_deferred_forest(core,plan,lambda:None)
            residual=set(plan['remaining_rows'])
            self.assertEqual(literal_residual(walks,set(tree)),residual)
            success=False
            for chosen in combinations(range(len(edges)),n-1):
                acyclic,labels=components(n,edges,chosen)
                if not acyclic or len(set(labels))!=1:continue
                expected=literal_residual(walks,set(chosen));self.assertLessEqual(residual,expected)
                success |= not expected;examined+=1
            result=core_handlebody_certificate(core,defer_forest=True)
            self.assertEqual(result['status']=='COMPLETE',success)
            if success:self.assertTrue(verify_core_handlebody_certificate(core,result['certificate']))
            else:self.assertEqual(result['reason'],'all_lower_forests_raw_obstruction')
        self.assertGreater(examined,300)

    def test_bridge_multiplicity_loops_components_and_invalid_charts(self):
        core=abstract_core(4,[(0,1),(1,1),(2,3),(3,3)],[[0,1,0],[2,3,2]])
        r=core_handlebody_certificate(core,defer_forest=True)
        self.assertEqual(r['certificate']['forest'],[0,2])
        self.assertTrue(verify_core_handlebody_certificate(core,r['certificate']))
        malformed=abstract_core(2,[(0,1)],[[0]])
        with self.assertRaisesRegex(ArithmeticError,'disconnected'):
            core_handlebody_certificate(malformed,defer_forest=True)

    def test_120_native_cores_with_unchanged_independent_checker(self):
        counts=[0,0]
        for c in BANK+EXTRA:
            g=geometry(c);core=reduce_core_three_handles(g,strategy='max_weight')[0]['core'];original=deepcopy(core)
            old=core_handlebody_certificate(core);new=core_handlebody_certificate(core,defer_forest=True)
            self.assertEqual(core,original)
            for i,r in enumerate((old,new)):
                counts[i]+=r['status']=='COMPLETE'
                if r['status']=='COMPLETE':self.assertTrue(verify_core_handlebody_certificate(core,r['certificate']))
            if old['status']=='COMPLETE':self.assertEqual(new['status'],'COMPLETE')
        self.assertEqual(counts,[112,118])

    def test_new_absorbed_cut_and_shared_three_attempt_queries(self):
        c=next(c for c in BANK if c['id']=='pachner23_5_8_2/mixed');args=c['triangulation'],c['coordinates']
        with patch('fastunknot.normal_cut_handlebodies.normal_cut_parallelity',wraps=normal_cut_parallelity) as source:
            with patch('fastunknot.normal_cut_handlebodies.normal_parallelity_boundary_words',wraps=normal_parallelity_boundary_words) as boundary:
                a=normal_cut_handlebodies(*args,record_certificate=True)
                self.assertEqual(source.call_count,1);self.assertEqual(boundary.call_count,1)
        self.assertEqual([r['strategy'] for r in a['stats']['lower_forest_attempts']],['source','max_passages','deferred'])
        self.assertEqual(a['status'],'COMPLETE');self.assertEqual(a['certificate']['schema'],'normal-cut-handlebodies-v2')
        canonical=select_core_forest(geometry(c)['core'],strategy='source')
        with patch('fastunknot.normal_cut_handlebodies.select_core_forest',return_value=canonical):
            skipped=normal_cut_handlebodies(*args,record_certificate=True)
        self.assertEqual([t['strategy'] for t in skipped['stats']['lower_forest_attempts']],['source','deferred'])
        self.assertEqual(skipped['certificate'],a['certificate'])
        b=normal_cut_handlebodies(*args,lower_forest='deferred',record_certificate=True)
        self.assertEqual(a['certificate'],b['certificate'])
        self.assertTrue(verify_normal_cut_handlebodies(*args,a['certificate']))
        bare=core_handlebody_certificate(geometry(c)['core'],defer_forest=True)
        self.assertNotEqual(bare['certificate']['forest'],a['certificate']['core']['forest'])
        plain=normal_cut_handlebodies(*args);self.assertEqual(plain['census'],a['census']);self.assertNotIn('certificate',plain)
        m=normal_cut_handlebodies(*args,boundary_method='moments',record_certificate=True)
        self.assertEqual(m['census'],a['census'])
        cycles=sum(s['orbit_cycles'] for s in m['stats']['parallelity'].values())+m['stats']['boundary']['census']['orbit_cycles']
        exact=normal_cut_handlebodies(*args,boundary_method='moments',record_certificate=True,max_cycles=cycles)
        self.assertEqual(exact['certificate'],m['certificate'])
        self.assertEqual(normal_cut_handlebodies(*args,boundary_method='moments',max_cycles=cycles-1)['status'],'INCONCLUSIVE')
        count=operations(m['certificate'])
        self.assertTrue(verify_normal_cut_handlebodies(*args,m['certificate'],max_operations=count))
        self.assertFalse(verify_normal_cut_handlebodies(*args,m['certificate'],max_operations=count-1))

    def test_full_kernel_rows_and_producer_independent_replay(self):
        c=next(c for c in BANK if c['id']=='pilot/fibonacci_lst_08/0');args=c['triangulation'],c['coordinates']
        with patch('fastunknot.bundle_boundary_kernel._deferred_forest',wraps=_deferred_forest) as choose:
            r=normal_cut_handlebodies(*args,lower_forest='deferred',record_certificate=True)
            self.assertEqual(choose.call_count,1)
        p=r['certificate'];self.assertEqual(p['kernel']['schema'],'bundle-boundary-kernel-v3')
        core,plan,_=choose.call_args.args
        circles=sum(a['kind']=='circle' for a in p['boundary']['skeleton']['attachment_components'])
        self.assertEqual(len(plan['cancellations']),len(core['handles2'])+circles)
        self.assertGreater(circles,0)
        with ExitStack() as stack:
            for name in ('fastunknot.core_handlebody._deferred_forest','fastunknot.bundle_boundary_kernel._deferred_forest',
                         'fastunknot.bundle_boundary_kernel.bundle_boundary_kernel'):
                stack.enter_context(patch(name,side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(*args,p))
        bad=deepcopy(p);bad['kernel']['forest'].pop();self.assertFalse(verify_normal_cut_handlebodies(*args,bad))

    def test_strict_options_and_callback(self):
        core=abstract_core(1,[(0,0)],[[0]])
        for bad in (None,0,1,'yes',[]):
            with self.assertRaises(ValueError):core_handlebody_certificate(core,defer_forest=bad)
            with self.assertRaises(ValueError):bundle_boundary_kernel({}, {}, {},defer_forest=bad)
        with self.assertRaises(ValueError):core_handlebody_certificate(core,forest=[],defer_forest=True)
        with self.assertRaises(ValueError):bundle_boundary_kernel({}, {}, {},forest=[],defer_forest=True)
        def stop():raise RuntimeError('stop')
        with self.assertRaisesRegex(RuntimeError,'stop'):core_handlebody_certificate(core,defer_forest=True,check=stop)
        with self.assertRaisesRegex(RuntimeError,'stop'):bundle_boundary_kernel({}, {}, {},defer_forest=True,check=stop)


if __name__=='__main__':unittest.main()
