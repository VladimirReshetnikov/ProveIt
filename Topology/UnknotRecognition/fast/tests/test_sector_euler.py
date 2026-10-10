"""Euler functional and corner screening against actual source surfaces."""
from itertools import product
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import sector_rays
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.sector_residual import _plan_window
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_euler import SourceEuler
from fastunknot.sector_window_basis import projected_corner_forms
from fastunknot.normal_disk_kernel import normal_compressing_disk_count,_count_prepared_discs,verify_normal_disk_count_certificate
from planar_sector_research.fixtures import double_capped_fibonacci


class SectorEulerTests(unittest.TestCase):
    def test_every_small_window_screen_agrees_with_fresh_complete_source_rays(self):
        raw=double_capped_fibonacci(1)['triangulation'];source=PreparedSectorSource(raw)
        checked=pruned=0
        for signature in product((-1,0,1,2),repeat=3):
            base=source.build([(t,q)for t,q in enumerate(signature)if q>=0])
            rays=list(sector_rays(base))
            rows=[[sum(v[t][j]for v in rays)for j in range(7)]for t in range(3)]
            support=[(t,q)for t,row in enumerate(rows)for q in range(3)if row[4+q]]
            base=source.build(support)
            plan=_plan_window(source.prepared,rows,2,lambda:None,base.basis)
            model=plan['_matching_updates'];euler=SourceEuler(source.prepared,model.potentials,lambda:None)
            for edits in plan['edits']:
                support,basis=model.for_edits(edits,lambda:None)
                fresh=source.build(support);rays=list(sector_rays(fresh))
                forms=projected_corner_forms(support,basis,model.potentials,lambda:None)
                envelope=euler.aggregate(support,basis,forms,lambda:None)
                stats=dict(euler_screens=0,euler_corners=0,euler_pruned_sectors=0)
                excluded=euler.excludes_positive(support,basis,forms,lambda:None,stats)
                self.assertEqual(excluded,not any(_coordinates(source.prepared,r,lambda:None)['euler_characteristic']>0 for r in rays))
                for r in rays:
                    # The compiler is checked against matching/edge geometry,
                    # including enormous coordinate scale without expansion.
                    for scale in (1,2**90+1):
                        scaled=[[scale*x for x in row]for row in r]
                        parameters=[scaled[support[p][0]][4+support[p][1]]for vector in basis
                                    for p in [next(i for i in range(len(support)-1,-1,-1)if vector[i])]]
                        expected=_coordinates(source.prepared,scaled,lambda:None)['euler_characteristic']
                        self.assertEqual(euler.canonical_value(support,basis,forms,parameters,lambda:None),expected)
                        self.assertEqual(euler.aggregated_value(envelope,parameters,lambda:None),expected)
                        self.assertEqual(sum(a*b for row,coefs in zip(scaled,euler.coefficients)for a,b in zip(row,coefs)),expected)
                checked+=1;pruned+=excluded
        self.assertGreater(checked,100);self.assertGreater(pruned,0)

    def test_anchor_shift_preserves_values_and_constant_groups_drop_out(self):
        fixture=double_capped_fibonacci(3);raw=fixture['triangulation'];source=PreparedSectorSource(raw)
        kernel=source.build(fixture['allowed_types'])
        rays=list(sector_rays(kernel));rows=[[sum(r[t][j]for r in rays)for j in range(7)]for t in range(len(raw['tetrahedra']))]
        model=_plan_window(source.prepared,rows,2,lambda:None,kernel.basis)['_matching_updates']
        euler=SourceEuler(source.prepared,model.potentials,lambda:None)
        forms=projected_corner_forms(kernel.support,kernel.basis,model.potentials,lambda:None)
        envelope=euler.aggregate(kernel.support,kernel.basis,forms,lambda:None)
        self.assertLessEqual(envelope[2],8*len(kernel.support))
        for parameter in ((1,0,0),(0,1,0),(0,0,1),(1,2,3)):
            self.assertEqual(euler.aggregated_value(envelope,parameter,lambda:None),
                euler.canonical_value(kernel.support,kernel.basis,forms,parameter,lambda:None))
        # Add an arbitrary source-group offset to every corner, and update
        # the signed linear term by its exact link contribution. The grouped
        # canonical functional must cancel that gauge change.
        shifted=list(forms);linear=list(euler.linear)
        free=[next(i for i in range(len(kernel.support)-1,-1,-1)if row[i])for row in kernel.basis]
        for corners,weight in euler.groups:
            offset=(17,-5,9)
            for c in corners:shifted[c]=tuple(a+b for a,b in zip(forms[c],offset))
            for p,value in zip(free,offset):
                t,typ=kernel.support[p];linear[3*t+typ]+=weight*value
        euler.linear=tuple(linear)
        shifted_envelope=euler.aggregate(kernel.support,kernel.basis,shifted,lambda:None)
        for parameter in ((1,0,0),(0,1,0),(0,0,1),(1,2,3)):
            self.assertEqual(euler.aggregated_value(shifted_envelope,parameter,lambda:None),
                euler.aggregated_value(envelope,parameter,lambda:None))
        # A constant group contributes only to the linear term.
        constant=[(2,3,5)]*len(forms)
        result=euler.aggregate(kernel.support,kernel.basis,constant,lambda:None)
        self.assertEqual(result[1],());self.assertEqual(result[2],0)

    def test_positive_first_corner_does_not_compile_an_unused_aggregation(self):
        fixture=double_capped_fibonacci(2);raw=fixture['triangulation'];source=PreparedSectorSource(raw)
        kernel=source.build(fixture['allowed_types']);rays=list(sector_rays(kernel))
        rows=[[sum(r[t][j]for r in rays)for j in range(7)]for t in range(len(raw['tetrahedra']))]
        model=_plan_window(source.prepared,rows,2,lambda:None,kernel.basis)['_matching_updates']
        euler=SourceEuler(source.prepared,model.potentials,lambda:None)
        forms=projected_corner_forms(kernel.support,kernel.basis,model.potentials,lambda:None)
        stats=dict(euler_screens=0,euler_corners=0,euler_pruned_sectors=0)
        with patch.object(euler,'aggregate',side_effect=AssertionError('unused aggregation')):
            self.assertFalse(euler.excludes_positive(kernel.support,kernel.basis,forms,lambda:None,stats))

    def test_above_planar_nullity_continues_without_an_exclusion(self):
        fixture=double_capped_fibonacci(1);raw=fixture['triangulation']
        raw['tetrahedra'][1][0]={'tetrahedron':3,'permutation':[0,1,2,3]}
        raw['tetrahedra'].append([{'tetrahedron':1,'permutation':[0,1,2,3]},None,None,None])
        source=PreparedSectorSource(raw);base=source.build(fixture['allowed_types'])
        rays=list(sector_rays(base))
        rows=[[sum(r[t][j]for r in rays)for j in range(7)]for t in range(4)]
        plan=_plan_window(source.prepared,rows,1,lambda:None,base.basis)
        model=plan['_matching_updates']
        support,basis=model.for_edits(((3,0),),lambda:None)
        self.assertEqual(len(basis),4)
        forms=projected_corner_forms(support,basis,model.potentials,lambda:None)
        euler=SourceEuler(source.prepared,plan['_matching_updates'].potentials,lambda:None)
        stats=dict(euler_screens=0,euler_corners=0,euler_pruned_sectors=0)
        self.assertFalse(euler.excludes_positive(support,basis,forms,lambda:None,stats))
        self.assertEqual(stats,dict(euler_screens=0,euler_corners=0,euler_pruned_sectors=0))

    def test_prepared_observer_preserves_real_disc_proofs_and_independent_replay(self):
        raw=double_capped_fibonacci(2)['triangulation'];source=PreparedSectorSource(raw)
        kernel=source.build(double_capped_fibonacci(2)['allowed_types'])
        checked=0
        for vector in sector_rays(kernel):
            expected=normal_compressing_disk_count(raw,vector,max_cycles=0,record_certificate=True)
            analysed=_coordinates(source.prepared,vector,lambda:None)
            # Producer reuse is real; the independent verifier is invoked
            # after the producer-only restriction has been removed.
            with patch('fastunknot.normal_disk_kernel._prepare',side_effect=AssertionError('source rebuilt in prepared observer')):
                actual=_count_prepared_discs(raw,source.prepared,analysed,max_cycles=0,record_certificate=True)
            self.assertEqual(actual,expected)
            if actual['status']=='COMPLETE':
                self.assertTrue(verify_normal_disk_count_certificate(raw,vector,actual['certificate']))
            checked+=1
        self.assertEqual(checked,7)


if __name__=='__main__':unittest.main()
