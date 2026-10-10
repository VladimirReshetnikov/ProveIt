"""Adaptive native selection of complete minimum-envelope standard rays."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import build_sector_kernel,enumerate_sector,discover_in_sector,SearchLimit
from fastunknot.normal_sector_verify import verify_sector_witness,verify_sector_exhaustion
from fastunknot.sector_envelope_certificate import certify_sector_enumeration
from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
from sector_envelope_research.fixtures import capped_fibonacci
from tests.test_sector_envelope import solid_torus


class SectorEnvelopeIntegrationTests(unittest.TestCase):
    def test_auto_uses_minima_without_hyperplanes_or_rank_filters(self):
        for n in (1,4,8):
            source=capped_fibonacci(n,1);raw,allowed=source['triangulation'],source['allowed_types']
            old,old_stats=enumerate_sector(raw,allowed,method='arrangement')
            with patch('fastunknot.normal_sector._hyperplanes',side_effect=AssertionError), \
                 patch('fastunknot.normal_sector.SectorKernel.is_standard_ray',side_effect=AssertionError):
                new,stats=enumerate_sector(raw,allowed)
            self.assertEqual({tuple(v for r in x for v in r) for x in old},
                             {tuple(v for r in x for v in r) for x in new})
            self.assertEqual(stats['method'],'envelope')
            self.assertEqual(stats['bases_attempted'],len(new))
            self.assertEqual(stats['hyperplanes'],0)
            self.assertEqual(stats['nonextreme_directions'],0)
            self.assertEqual(old_stats['positive_directions'],n+2)
            self.assertEqual(old_stats['nonextreme_directions'],n-1)

    def test_standard_discovery_has_source_bound_positive_and_negative_replay(self):
        source=capped_fibonacci(8,1);raw,allowed=source['triangulation'],source['allowed_types']
        for method in ('auto','envelope','arrangement'):
            result=discover_in_sector(raw,allowed,phase='standard',method=method)
            self.assertEqual(result['status'],'DISC_FOUND')
            self.assertTrue(verify_sector_witness(raw,result['certificate']))
        negative=discover_in_sector(solid_torus(),[],phase='standard')
        self.assertEqual(negative['status'],'NO_POSITIVE_EULER')
        self.assertTrue(verify_sector_exhaustion(solid_torus(),negative['certificate']))

    def test_caps_count_actual_lifts_and_reject_partial_completeness(self):
        source=capped_fibonacci(8,1);raw,allowed=source['triangulation'],source['allowed_types']
        rays,stats=enumerate_sector(raw,allowed,max_bases=3)
        self.assertEqual(len(rays),3)
        with self.assertRaises(SearchLimit):enumerate_sector(raw,allowed,max_bases=2)
        partial=certify_sector_enumeration(raw,allowed,max_rays=2)
        self.assertEqual(partial['status'],'INCONCLUSIVE')
        self.assertNotIn('certificate',partial);self.assertNotIn('coordinates',partial)
        complete=certify_sector_enumeration(raw,allowed,max_rays=3)
        self.assertTrue(verify_sector_envelope_certificate(raw,complete['certificate']))
        limited=discover_in_sector(raw,allowed,phase='standard',max_bases=0)
        self.assertEqual(limited['status'],'INCONCLUSIVE');self.assertNotIn('certificate',limited)

    def test_quadrilateral_and_explicit_method_contracts_are_preserved(self):
        source=capped_fibonacci(4,1);raw,allowed=source['triangulation'],source['allowed_types']
        q,stats=enumerate_sector(raw,allowed,phase='quadrilateral')
        self.assertEqual(stats['method'],'arrangement')
        self.assertEqual(len(q),2)
        for method in ('envelope','supports','unknown',None):
            with self.assertRaises(ValueError):enumerate_sector(raw,allowed,phase='quadrilateral',method=method)
            with self.assertRaises(ValueError):discover_in_sector(raw,allowed,method=method)
        empty,stats=enumerate_sector(raw,[])
        self.assertEqual(empty,[]);self.assertEqual(stats['method'],'empty')

    def test_coverage_checker_accepts_legacy_basis_choices_and_rejects_omissions(self):
        source=capped_fibonacci(4,1);raw,allowed=source['triangulation'],source['allowed_types']
        proof=certify_sector_enumeration(raw,allowed)['certificate']
        with patch('fastunknot.normal_sector.build_sector_kernel',side_effect=AssertionError), \
             patch('fastunknot.sector_envelope.sector_envelope_plan',side_effect=AssertionError), \
             patch('fastunknot.sector_envelope.sector_envelope_rays',side_effect=AssertionError):
            self.assertTrue(verify_sector_envelope_certificate(raw,proof))
        for i in range(len(proof['rays'])):
            bad=deepcopy(proof);bad['rays'].pop(i)
            self.assertFalse(verify_sector_envelope_certificate(raw,bad))


if __name__=='__main__':unittest.main()
