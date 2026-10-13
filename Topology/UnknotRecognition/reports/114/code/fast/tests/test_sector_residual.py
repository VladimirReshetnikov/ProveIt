"""Literal type windows, new diagram discs and independent source replay."""
from contextlib import ExitStack
from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_sector import build_sector_kernel,sector_rays
from fastunknot.normal_sector_verify import dense_sector_model
from fastunknot.normal_disk_kernel import normal_compressing_disk_count
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.sector_residual import plan_sector_window
from planar_sector_research.fixtures import double_capped_fibonacci,capped_fibonacci,vector_key


def support(signature):return [(t,q)for t,q in enumerate(signature)if q>=0]
def signature(rows):return tuple(next((q for q in range(3)if row[4+q]),-1)for row in rows)


class SectorResidualTests(unittest.TestCase):
    def test_filter_covers_every_ray_in_literal_small_type_windows(self):
        for raw in (capped_fibonacci(1)['triangulation'],double_capped_fibonacci(1)['triangulation']):
            n=len(raw['tetrahedra']);all_rays={}
            for sig in product((-1,0,1,2),repeat=n):
                k=build_sector_kernel(raw,support(sig))
                all_rays[sig]=list(sector_rays(k))
            bases=[[[0]*7 for _ in range(n)]]
            bases += [rays[0]for rays in all_rays.values()if rays][:12]
            for rows in bases:
                base=signature(rows)
                for radius in (1,2):
                    plan=plan_sector_window(raw,rows,radius=radius)
                    independent=dense_sector_model(raw,support(base))
                    self.assertEqual(plan['stats']['base_nullity'],len(independent['basis']))
                    expected={vector_key(v)for sig,values in all_rays.items()
                        if sum(a!=b for a,b in zip(base,sig))<=radius for v in values}
                    observed=set()
                    for edits in plan['edits']:
                        sig=list(base)
                        for t,q in edits:sig[t]=q
                        observed.update(vector_key(v)for v in all_rays[tuple(sig)])
                    self.assertEqual(observed,expected)
                    self.assertEqual(len(plan['edits']),len(set(plan['edits'])))

    def test_known_coherent_miss_gets_a_source_certified_normal_disc(self):
        d=Diagram.from_braid(2,[1,1,-1])
        self.assertEqual(normal_seed_decide(d)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d,sector_radius=1)['status'],'INCONCLUSIVE')
        answer=normal_seed_decide(d,sector_radius=2,max_cycles=0)
        self.assertEqual(answer['status'],'UNKNOT')
        self.assertEqual(answer['certificate']['schema'],'diagram-normal-disc-v1')
        self.assertEqual(answer['stats']['sector_search']['orbit_cycles'],0)
        self.assertEqual(answer['stats']['sector_search']['sectors_queried'],32)
        self.assertTrue(verify_normal_seed_certificate(d,answer['certificate']))
        disabled=['fastunknot.sector_residual.plan_sector_window','fastunknot.sector_residual._plan_window',
            'fastunknot.sector_residual._full_quad_columns','fastunknot.sector_residual.search_sector_window',
            'fastunknot.normal_seed.normal_seed_decide','fastunknot.normal_sector.build_sector_kernel',
            'fastunknot.normal_disk_kernel.normal_compressing_disk_count',
            'fastunknot.normal_disk_kernel.canonical_disk_core','fastunknot.interval_orbits.count_orbits']
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
            self.assertTrue(verify_normal_seed_certificate(d,answer['certificate']))
        for field in answer['certificate']:
            bad=deepcopy(answer['certificate']);del bad[field]
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        bad=deepcopy(answer['certificate']);bad['coordinates'][0][0]+=1
        self.assertFalse(verify_normal_seed_certificate(d,bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),answer['certificate']))

    def test_shelling_trace_can_authenticate_an_ordinary_disc_proof(self):
        d=Diagram.from_braid(2,[1]);answer=normal_seed_decide(d,shellings=True)
        wrapped=deepcopy(answer['certificate']);inner=wrapped['surface_certificate']
        counted=normal_compressing_disk_count(inner['triangulation'],inner['coordinates'],record_certificate=True)
        wrapped['surface_certificate']=dict(schema='diagram-normal-disc-v1',input_pd=inner['input_pd'],
            triangulation=inner['triangulation'],coordinates=inner['coordinates'],disc_certificate=counted['certificate'])
        self.assertTrue(wrapped['shellings']);self.assertTrue(verify_normal_seed_certificate(d,wrapped))
        bad=deepcopy(wrapped);bad['shellings'].pop()
        self.assertFalse(verify_normal_seed_certificate(d,bad))

    def test_shared_work_limits_and_callback_exceptions_remain_effective(self):
        d=Diagram.from_braid(2,[1,1,-1]);answer=normal_seed_decide(d,sector_radius=2)
        capped=normal_seed_decide(d,sector_radius=2,max_work=answer['work']-1)
        self.assertEqual(capped['status'],'INCONCLUSIVE');self.assertNotIn('certificate',capped)
        proof=answer['certificate'];calls=[0]
        def count():calls[0]+=1
        self.assertTrue(verify_normal_seed_certificate(d,proof,check=count));total=calls[0]
        class Stop:
            def __init__(self,n,error):self.n=n;self.error=error
            def __bool__(self):return False
            def __call__(self):
                self.n-=1
                if self.n==0:raise self.error('source replay cancelled')
        for error in (ValueError,NormalOrbitError):
            for n in (1,total//2,total):
                with self.assertRaisesRegex(error,'source replay cancelled'):
                    verify_normal_seed_certificate(d,proof,check=Stop(n,error))
        with self.assertRaisesRegex(ValueError,'source replay cancelled'):
            normal_seed_decide(d,sector_radius=2,check=Stop(20,ValueError))

    def test_flags_and_complete_recognition_use_the_new_source_proof(self):
        d=Diagram.from_braid(2,[1,1,-1])
        for invalid in (True,-1,3,1.5):
            with self.assertRaises(ValueError):normal_seed_decide(d,sector_radius=invalid)
            with self.assertRaises(ValueError):recognize(d,normal_seed_sector_radius=invalid)
        result=recognize(d,use_reduction=False,use_descending=False,use_seifert=False,
            use_braid=False,use_rational=False,use_factorization=False,use_modular=False,
            use_jones=False,use_alexander=False,use_r3=False,use_normal_seed=True,
            normal_seed_sector_radius=2,seconds=10)
        self.assertEqual(result.status,'UNKNOT');self.assertEqual(result.method,'native-normal-sector-window')
        self.assertTrue(verify_normal_seed_certificate(d,result.evidence['normal_seed']['certificate']))
        with tempfile.TemporaryDirectory()as temporary:
            path=Path(temporary)/'diagram.json';path.write_text(json.dumps({'pd':d.pd}))
            command=[sys.executable,'-B','-m','fastunknot','recognize',str(path),
                '--normal-seed','--normal-seed-sector-radius','2','--no-reduction','--no-descending',
                '--no-seifert','--no-braid','--no-rational','--no-factor','--no-alexander','--no-jones']
            cli=subprocess.run(command,capture_output=True,text=True,check=True)
            decoded=json.loads(cli.stdout)
            self.assertEqual(decoded['status'],'UNKNOT')
            self.assertEqual(decoded['method'],'native-normal-sector-window')


if __name__=='__main__':unittest.main()
