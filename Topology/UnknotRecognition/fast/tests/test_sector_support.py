"""Feasible-span recompilation retains the original sector's proof authority."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import _discover_in_kernel,build_sector_kernel,sector_rays
from fastunknot.normal_sector_verify import verify_sector_exhaustion

BANK=Path(__file__).resolve().parents[2]/'reports/57/results/discovery_corpus.json'

def fixture(caps=2):
    raw=next(r['triangulation']for r in json.loads(BANK.read_text())['records']if r['id']==f'cap_3_5_{caps}')
    support=[(0,0),(1,1),(2,2),(3,0),(4,1)]if caps==2 else [(0,0),(1,1),(2,2),(3,0),(4,2),(5,2)]
    return raw,support


def discover_in_sector(raw,support,**kwargs):
    # Exercise the complete-Q support route independently of the newer
    # sufficient matching-row preprocessor.
    return _discover_in_kernel(build_sector_kernel(raw,support),matching_first=False,**kwargs)


class FeasibleSupportTests(unittest.TestCase):
    def test_completed_Q_phase_admits_planar_enumeration_with_original_support(self):
        raw,support=fixture();answer=discover_in_sector(raw,support,phase='standard',max_bases=9)
        self.assertEqual(answer['status'],'NO_VERTEX_DISC_IN_SECTOR')
        self.assertEqual(answer['stats']['method'],'planar')
        self.assertEqual(answer['stats']['matching_nullity'],3)
        self.assertEqual(answer['stats']['support_reduction']['requested_kernel']['matching_nullity'],4)
        self.assertEqual(answer['stats']['support_reduction']['retained_indices'],[0,3,4])
        self.assertEqual(answer['stats']['bases_attempted'],9)
        proof=answer['certificate'];self.assertEqual(proof['allowed_types'],[list(x)for x in support])
        self.assertEqual(proof['q_support_certificate']['allowed_types'],proof['allowed_types'])
        self.assertEqual(len(proof['rays']),5)
        self.assertTrue(all(len(r['quadrilaterals'])==5 and not any(r['quadrilaterals'][i]for i in (1,2))for r in proof['rays']))
        self.assertTrue(verify_sector_exhaustion(raw,proof))
        legacy=deepcopy(proof);legacy.pop('q_support_certificate')
        self.assertTrue(verify_sector_exhaustion(raw,legacy))
        original=list(sector_rays(build_sector_kernel(raw,support)))
        self.assertEqual({tuple(r['quadrilaterals'])for r in proof['rays']},
                         {tuple(rows[t][4+q]for t,q in support)for rows in original})

    def test_partial_Q_phase_and_shared_standard_cap_never_certify_forced_zeros(self):
        raw,support=fixture()
        for cap in (0,3,4,8):
            answer=discover_in_sector(raw,support,phase='standard',max_bases=cap)
            self.assertEqual(answer['status'],'INCONCLUSIVE')
            self.assertEqual(answer['stats']['bases_attempted'],cap)
            self.assertNotIn('certificate',answer)
            if cap<4:self.assertNotIn('support_reduction',answer['stats'])
        self.assertEqual(discover_in_sector(raw,support,phase='standard',max_bases=9)['status'],
                         'NO_VERTEX_DISC_IN_SECTOR')

    def test_reduced_generic_branch_preserves_full_source_certificate(self):
        raw,support=fixture(3);answer=discover_in_sector(raw,support,phase='standard')
        self.assertEqual(answer['status'],'NO_VERTEX_DISC_IN_SECTOR')
        self.assertEqual(answer['stats']['matching_nullity'],4)
        self.assertEqual(answer['stats']['support_reduction']['requested_kernel']['matching_nullity'],5)
        self.assertEqual(answer['stats']['support_reduction']['retained_indices'],[0,3,4,5])
        self.assertEqual(answer['certificate']['allowed_types'],[list(x)for x in support])
        self.assertTrue(verify_sector_exhaustion(raw,answer['certificate']))

    def test_nested_support_proof_mutations_are_rejected_without_producers(self):
        raw,support=fixture();proof=discover_in_sector(raw,support,phase='standard')['certificate']
        mutations=[]
        item=deepcopy(proof);item['q_support_certificate']['rays'].pop();mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['allowed_types'].pop();mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['source_sha256']='0'*64;mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['phase']='standard';mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['status']='NO_POSITIVE_EULER';mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['rays'][0]['quadrilaterals'][0]+=1;mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']['q_support_certificate']=deepcopy(item['q_support_certificate']);mutations.append(item)
        item=deepcopy(proof);item['q_support_certificate']=None;mutations.append(item)
        item=deepcopy(proof);item['rays'][0]['quadrilaterals'][1]=1;mutations.append(item)
        item=deepcopy(proof);item['rays'].pop();mutations.append(item)
        item=deepcopy(proof);item['rays'][0]['euler_characteristic']+=1;mutations.append(item)
        disabled=('fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
                  'fastunknot.normal_sector._discover_in_kernel','fastunknot.sector_euler._q_corner_parameters',
                  'fastunknot.sector_planar.sector_planar_rays','fastunknot.sector_euler.SourceEuler.__init__')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer invoked during replay')))
            self.assertTrue(verify_sector_exhaustion(raw,proof))
            for item in mutations:self.assertFalse(verify_sector_exhaustion(raw,item))

    def test_interruption_during_support_recompilation_propagates(self):
        raw,support=fixture()
        from fastunknot import normal_sector
        original=normal_sector.build_sector_kernel
        def build(source,allowed,**kwargs):
            if len(allowed)<len(support):raise InterruptedError('recompilation interrupted')
            return original(source,allowed,**kwargs)
        with patch.object(normal_sector,'build_sector_kernel',side_effect=build):
            with self.assertRaises(InterruptedError):discover_in_sector(raw,support,phase='standard')


if __name__=='__main__':unittest.main()
