"""Source dual forests, repeated endpoints, and whole-cut v6 proof binding."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from tests.test_normal_components import relabel
ROOT=Path(__file__).parents[1]
BANK=json.loads((ROOT/'marked_parallelity_research/corpus.json').read_text())['cases']
EXTRA=json.loads((ROOT/'marked_parallelity_research/three_handle_corpus.json').read_text())['cases']


def geometry(c):
    p=_prepare(c['triangulation'],lambda:None)
    return _parallelity_geometry(p,_coordinates(p,c['coordinates'],lambda:None),lambda:None)


class CoreThreeHandleTests(unittest.TestCase):
    def checked(self,g):
        before=deepcopy(g);reduced,proof=reduce_core_three_handles(g)
        self.assertEqual(g,before)
        self.assertEqual(replay_core_three_handles(g,proof),reduced)
        self.assertFalse(reduced['core']['handles3'])
        self.assertEqual(len(proof['cancellations']),len(g['core']['handles3']))
        self.assertEqual(len(g['core']['handles2'])-len(reduced['core']['handles2']),len(proof['cancellations']))
        for k in ('handles0','handles1'):self.assertEqual(reduced['core'][k],g['core'][k])
        self.assertEqual(reduced['ports'],g['ports'])
        return reduced,proof

    def test_all_106_sources_and_nested_interior_forests(self):
        saw_chain=False
        for c in BANK+EXTRA:
            _,proof=self.checked(geometry(c))
            ends={r['two_handle']:r['ends'] for r in proof['dual_endpoints']}
            saw_chain |= any(all(v is not None for v in ends[m['two_handle']]) for m in proof['cancellations'])
        self.assertTrue(saw_chain)

    def test_source_loop_is_two_occurrences_not_a_unit_pivot(self):
        g=geometry(next(c for c in EXTRA if c['id']=='interior_loop/empty'))
        _,proof=self.checked(g)
        loop=next(r for r in proof['dual_endpoints'] if r['ends'][0] is not None and r['ends'][0]==r['ends'][1])
        bad=deepcopy(proof);bad['cancellations'][0]=dict(two_handle=loop['two_handle'],three_handle=loop['ends'][0])
        self.assertIsNone(replay_core_three_handles(g,bad))
        self.assertNotEqual(proof['cancellations'][0]['two_handle'],loop['two_handle'])

    def test_hostile_records_and_source_binding(self):
        g=geometry(next(c for c in EXTRA if c['id']=='nested_1_4_6/empty'));_,proof=self.checked(g)
        mutations=[lambda p:p.update(schema='wrong'),lambda p:p.update(extra=0),
                   lambda p:p['dual_endpoints'].pop(),
                   lambda p:p['dual_endpoints'][0]['ends'].__setitem__(0,True),
                   lambda p:p['cancellations'].pop(),lambda p:p['cancellations'].reverse(),
                   lambda p:p['cancellations'][0].update(two_handle=True),
                   lambda p:p['cancellations'][0].update(three_handle=-1),
                   lambda p:p['cancellations'][0].update(two_handle='0xgarbage'),
                   lambda p:p['cancellations'][0].update(extra=1),
                   lambda p:p['cancellations'].__setitem__(1,p['cancellations'][0]),
                   lambda p:p['surviving_two_handles'].pop(),lambda p:p['surviving_two_handles'].reverse()]
        for mutate in mutations:
            p=deepcopy(proof);mutate(p);self.assertIsNone(replay_core_three_handles(g,p))
        other=geometry(next(c for c in EXTRA if c['id']=='nested_1_4_6/boundary_link'))
        self.assertIsNone(replay_core_three_handles(other,proof))

    def test_replay_without_producer_helpers(self):
        g=geometry(next(c for c in BANK if c['id']=='interior_1_2/mixed'));reduced,proof=self.checked(g)
        names=('fastunknot.core_three_handle_reduction.reduce_core_three_handles',
               'fastunknot.core_three_handle_reduction._prepare',
               'fastunknot.core_three_handle_reduction._coordinates',
               'fastunknot.normal_parallelity_geometry._parallelity_geometry')
        with ExitStack() as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer called')))
            self.assertEqual(replay_core_three_handles(g,proof),reduced)

    def test_ten_old_refusals_and_seven_new_certificates(self):
        complete=0
        for c in BANK:
            if 'interior' not in c['id']:continue
            r=normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True)
            if r['status']=='COMPLETE':
                complete+=1;self.assertEqual(r['certificate']['schema'],'normal-cut-handlebodies-v6')
                self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],r['certificate']))
            else:self.assertNotIn('certificate',r)
        self.assertEqual(complete,7)

    def test_whole_proof_binding_independent_replay_and_caps(self):
        c=next(c for c in BANK if c['id']=='interior_1_2/mixed')
        r=normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True);p=r['certificate']
        names=('fastunknot.normal_cut_handlebodies.reduce_core_three_handles',
               'fastunknot.core_three_handle_reduction.reduce_core_three_handles',
               'fastunknot.normal_cut_handlebodies.bundle_boundary_kernel')
        with ExitStack() as stack:
            for name in names:stack.enter_context(patch(name,side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],p))
        bad=deepcopy(p);bad['core_reduction']['cancellations'][0]['three_handle']=True
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],bad))
        bad=deepcopy(p);bad['parallelity']['geometry']['core']['handles3'][0]['link_triangles'].pop()
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],bad))
        bad=deepcopy(p);bad['schema']='normal-cut-handlebodies-v5'
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],bad))
        self.assertFalse(verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],p,max_operations=0))
        self.assertEqual(normal_cut_handlebodies(c['triangulation'],c['coordinates'],max_cycles=0)['status'],'INCONCLUSIVE')
        other=normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True,precheck_core=False)
        self.assertEqual(other['certificate'],p)

    def test_binary_coordinates_hex_and_relabelled_sources(self):
        c=next(c for c in BANK if c['id']=='interior_1_2/mixed')
        rows=[[(1<<512)*v for v in row] for row in c['coordinates']]
        g=geometry(dict(c,coordinates=rows));reduced,proof=self.checked(g)
        for move in proof['cancellations']:
            for k in move:move[k]=hex(move[k])
        self.assertEqual(replay_core_three_handles(g,proof),reduced)
        r=normal_cut_handlebodies(c['triangulation'],rows,record_certificate=True)
        self.assertEqual(r['status'],'COMPLETE')
        self.assertTrue(verify_normal_cut_handlebodies(c['triangulation'],json_safe(rows),json_safe(r['certificate'])))
        rng=random.Random(26101263)
        for c in (EXTRA[-3],EXTRA[7],next(c for c in BANK if c['id']=='pilot/finite_trefoil_interior/0')):
            for _ in range(5):
                raw,rows=relabel(c['triangulation'],c['coordinates'],rng)
                self.checked(geometry(dict(c,triangulation=raw,coordinates=rows)))

    def test_callbacks_propagate(self):
        class Stop:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('cancelled')
        g=geometry(EXTRA[0]);_,proof=self.checked(g)
        with self.assertRaisesRegex(RuntimeError,'cancelled'):reduce_core_three_handles(g,check=Stop())
        with self.assertRaisesRegex(RuntimeError,'cancelled'):replay_core_three_handles(g,proof,check=Stop())


if __name__=='__main__':unittest.main()
