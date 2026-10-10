"""Source-derived kernel updates against complete fresh reconstruction."""
from itertools import product
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.normal_sector import sector_rays
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_residual import _plan_window,search_sector_window
from fastunknot.sector_window_basis import projected_window_kernel,projected_corner_forms
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from planar_sector_research.fixtures import double_capped_fibonacci,vector_key


class WindowBasisTests(unittest.TestCase):
    def test_every_small_window_update_matches_the_fresh_native_basis_and_rays(self):
        fixture=double_capped_fibonacci(1);raw=fixture['triangulation'];source=PreparedSectorSource(raw)
        queries=0
        for signature in product((-1,0,1,2),repeat=3):
            support=[(t,q)for t,q in enumerate(signature)if q>=0]
            old=source.build(support);rays=list(sector_rays(old))
            # Use actual positive support of a normal vector, including the
            # empty vector and multiple-ray sums rather than a forged cone.
            rows=[[sum(v[t][j]for v in rays)for j in range(7)]for t in range(3)]
            support=[(t,q)for t,row in enumerate(rows)for q in range(3)if row[4+q]]
            base=source.build(support);plan=_plan_window(source.prepared,rows,2,lambda:None,base.basis)
            for edits in plan['edits']:
                model=plan['_matching_updates']
                allowed,basis,projection=model.for_edits(edits,lambda:None,projection=True)
                fresh=source.build(allowed)
                self.assertEqual(basis,fresh.basis)
                forms=model.project_modes(projection,lambda:None)
                self.assertEqual(forms,projected_corner_forms(allowed,basis,model.potentials,lambda:None))
                updated=projected_window_kernel(raw,source.prepared,allowed,basis,
                    model.potentials,lambda:None,corner_forms=forms)
                actual=list(sector_rays(updated));expected=list(sector_rays(fresh))
                self.assertEqual({vector_key(v)for v in actual},{vector_key(v)for v in expected})
                self.assertEqual(len(actual),len(expected))
                for row in expected:
                    q=[row[t][4+kind]for t,kind in allowed]
                    self.assertEqual(updated.lift(q),row)
                    self.assertTrue(updated.is_standard_ray(row))
                queries+=1
        self.assertGreater(queries,100)

    def test_a_real_diagram_window_builds_one_full_basis_and_replays_its_disc(self):
        d=Diagram.from_braid(2,[1,1,-1]);raw=diagram_exterior(d);seed,_=_rank_one_cocycle_seed_details(raw)
        rows=minimize_cocycle_span(seed['vertices'],seed['heights'])['coordinates']
        build=PreparedSectorSource.build
        with patch.object(PreparedSectorSource,'build',autospec=True,side_effect=build)as calls:
            answer=search_sector_window(raw,rows,radius=2,max_cycles=0)
        self.assertEqual(calls.call_count,1);self.assertEqual(answer['status'],'DISC_FOUND')
        self.assertEqual(answer['stats']['full_basis_builds'],1)
        self.assertEqual(answer['stats']['basis_updates'],31)
        self.assertLessEqual(answer['stats']['base_potential_builds'],1)
        self.assertGreater(answer['stats']['mode_projections'],0)
        proof=dict(schema='diagram-normal-disc-v1',input_pd=[list(r)for r in d.pd],triangulation=raw,
            coordinates=answer['coordinates'],disc_certificate=answer['disc_certificate'])
        self.assertTrue(verify_normal_seed_certificate(d,proof))

    def test_updated_nullity_four_keeps_both_complete_generic_methods(self):
        f=double_capped_fibonacci(1);raw=f['triangulation']
        raw['tetrahedra'][1][0]={'tetrahedron':3,'permutation':[0,1,2,3]}
        raw['tetrahedra'].append([{'tetrahedron':1,'permutation':[0,1,2,3]},None,None,None])
        source=PreparedSectorSource(raw);base=source.build(f['allowed_types'])
        old=list(sector_rays(base))
        rows=[[sum(r[t][j]for r in old)for j in range(7)]for t in range(4)]
        plan=_plan_window(source.prepared,rows,1,lambda:None,base.basis)
        for q in range(3):
            model=plan['_matching_updates']
            allowed,basis,projection=model.for_edits(((3,q),),lambda:None,projection=True)
            self.assertEqual(len(basis),4)
            forms=model.project_modes(projection,lambda:None)
            self.assertEqual(forms,projected_corner_forms(allowed,basis,model.potentials,lambda:None))
            updated=projected_window_kernel(raw,source.prepared,allowed,basis,
                model.potentials,lambda:None,corner_forms=forms)
            fresh=source.build(allowed)
            for method in ('arrangement','supports'):
                self.assertEqual({vector_key(r)for r in sector_rays(updated,method=method)},
                    {vector_key(r)for r in sector_rays(fresh,method=method)})

    def test_interrupted_column_projection_is_not_published_to_the_cache(self):
        fixture=double_capped_fibonacci(1);source=PreparedSectorSource(fixture['triangulation'])
        base=source.build(fixture['allowed_types']);rays=list(sector_rays(base))
        rows=[[sum(r[t][j]for r in rays)for j in range(7)]for t in range(3)]
        model=_plan_window(source.prepared,rows,2,lambda:None,base.basis)['_matching_updates']
        item=next(iter(model.coefficients))
        class Interrupted(RuntimeError):pass
        calls=0
        def stop_during_column():
            nonlocal calls
            calls+=1
            if calls==3:raise Interrupted
        with self.assertRaises(Interrupted):model._corrected_column(item,stop_during_column,None)
        self.assertNotIn(item,model._column_modes)
        completed=model._corrected_column(item,lambda:None,None)
        self.assertEqual(len(completed),len(model.potentials))
        with patch.object(model,'_corrected_column',side_effect=AssertionError('unexpected new column')):
            support,basis,projection=model.for_edits((),lambda:None,projection=True)
            self.assertEqual(model.project_modes(projection,lambda:None),
                projected_corner_forms(support,basis,model.potentials,lambda:None))


if __name__=='__main__':unittest.main()
