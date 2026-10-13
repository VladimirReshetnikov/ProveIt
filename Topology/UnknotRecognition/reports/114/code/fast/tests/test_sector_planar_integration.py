"""Native adaptive dispatch and coverage for matching nullity three."""
from contextlib import ExitStack
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import enumerate_sector,discover_in_sector,SearchLimit,build_sector_kernel
from fastunknot.normal_sector_verify import verify_sector_witness
from fastunknot.sector_planar import certify_planar_sector
from fastunknot.sector_planar_verify import verify_planar_sector_certificate
from fastunknot.sector_sparse import PreparedSectorSource
from planar_sector_research.fixtures import double_capped_fibonacci,capped_fibonacci,vector_key


class PlanarSectorIntegrationTests(unittest.TestCase):
    def test_auto_nullity_three_has_no_pairwise_hyperplanes_or_rank_filter(self):
        for n in (1,2,4):
            source=double_capped_fibonacci(n);raw,allowed=source['triangulation'],source['allowed_types']
            old,_=enumerate_sector(raw,allowed,method='arrangement')
            with patch('fastunknot.normal_sector._hyperplanes',side_effect=AssertionError), \
                 patch('fastunknot.normal_sector.SectorKernel.is_standard_ray',side_effect=AssertionError):
                new,stats=enumerate_sector(raw,allowed)
            self.assertEqual({vector_key(v) for v in old},{vector_key(v) for v in new})
            self.assertEqual(stats['method'],'planar');self.assertEqual(stats['matching_dimension'],3)
            self.assertEqual(stats['bases_attempted'],7);self.assertEqual(stats['emitted_rays'],7)
            self.assertEqual(stats['nonextreme_directions'],0)

    def test_old_low_nullity_method_is_retained(self):
        for n in (1,4):
            source=capped_fibonacci(n);raw,allowed=source['triangulation'],source['allowed_types']
            old,stats=enumerate_sector(raw,allowed)
            planar,_=enumerate_sector(raw,allowed,method='planar')
            self.assertEqual(stats['method'],'envelope')
            self.assertEqual({vector_key(v) for v in old},{vector_key(v) for v in planar})
        source=double_capped_fibonacci(2)
        for method in ('auto','arrangement'):
            _,stats=enumerate_sector(source['triangulation'],source['allowed_types'],phase='quadrilateral',method=method)
            self.assertEqual(stats['method'],'arrangement')
        with self.assertRaises(ValueError):enumerate_sector(source['triangulation'],source['allowed_types'],phase='quadrilateral',method='planar')

    def test_actual_ray_caps_and_independent_coverage(self):
        source=double_capped_fibonacci(4);raw,allowed=source['triangulation'],source['allowed_types']
        rays,stats=enumerate_sector(raw,allowed,max_bases=7)
        self.assertEqual(len(rays),7)
        with self.assertRaises(SearchLimit):enumerate_sector(raw,allowed,max_bases=6)
        answer=certify_planar_sector(raw,allowed,max_rays=7)
        self.assertTrue(verify_planar_sector_certificate(raw,answer['certificate']))
        partial=certify_planar_sector(raw,allowed,max_rays=6)
        self.assertEqual(partial['status'],'INCONCLUSIVE');self.assertNotIn('certificate',partial)
        disabled=['fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
            'fastunknot.sector_planar.sector_planar_plan','fastunknot.sector_planar._clip_polygon',
            'fastunknot.sector_planar._projected_lift','fastunknot.sector_sparse.PreparedSectorSource.build']
        with ExitStack() as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in coverage replay')))
            self.assertTrue(verify_planar_sector_certificate(raw,answer['certificate']))
        for i in range(7):
            bad=deepcopy(answer['certificate']);bad['rays'].pop(i)
            self.assertFalse(verify_planar_sector_certificate(raw,bad))

    def test_native_discovery_and_reused_source_agree(self):
        source=double_capped_fibonacci(4);raw,allowed=source['triangulation'],source['allowed_types']
        answer=discover_in_sector(raw,allowed,phase='standard')
        self.assertEqual(answer['status'],'DISC_FOUND');self.assertTrue(verify_sector_witness(raw,answer['certificate']))
        shared=PreparedSectorSource(raw)
        first=certify_planar_sector(raw,allowed);second=certify_planar_sector(raw,allowed,source=shared)
        self.assertEqual(first['certificate'],second['certificate'])
        # Source reuse is explicit; existing one-shot construction is unchanged.
        a=build_sector_kernel(raw,allowed);b=shared.build(allowed)
        self.assertEqual(a.basis,b.basis);self.assertEqual(a.matrix,b.matrix)


if __name__=='__main__':unittest.main()
