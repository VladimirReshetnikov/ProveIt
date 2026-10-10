"""Source-row forcing and independent linear implication replay."""
from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import discover_in_sector,build_sector_kernel,_discover_in_kernel
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.sector_matching_support import matching_support,_closure,_kernel_equations
from test_sector_support import fixture


class MatchingSupportTests(unittest.TestCase):
    def test_source_equations_admit_planar_search_before_generic_Q_enumeration(self):
        raw,support=fixture()
        with patch('fastunknot.sector_euler._q_corner_parameters',side_effect=AssertionError('raw-dimensional Q scan')):
            result=discover_in_sector(raw,support,phase='standard',max_bases=5)
        self.assertEqual(result['status'],'NO_VERTEX_DISC_IN_SECTOR')
        self.assertEqual(result['stats']['matching_nullity'],3)
        self.assertEqual(result['stats']['bases_attempted'],5)
        self.assertNotIn('q_screen_stats',result['stats'])
        self.assertIn('matching_support_certificate',result['certificate'])
        self.assertNotIn('q_support_certificate',result['certificate'])
        self.assertEqual(result['certificate']['allowed_types'],[list(x)for x in support])
        self.assertTrue(verify_sector_exhaustion(raw,result['certificate']))
        legacy=deepcopy(result['certificate']);legacy.pop('matching_support_certificate')
        self.assertTrue(verify_sector_exhaustion(raw,legacy))
        partial=discover_in_sector(raw,support,phase='standard',max_bases=4)
        self.assertEqual(partial['status'],'INCONCLUSIVE');self.assertNotIn('certificate',partial)

    def test_source_forcing_finds_every_oracle_zero_in_retained_higher_nullity_bank(self):
        root=Path(__file__).resolve().parents[2]
        bank={r['id']:r for r in json.loads((root/'reports/57/results/discovery_corpus.json').read_text())['records']}
        prior=json.loads((root/'synthesis/data/feasible-span-audit.json').read_text())['source_cases']
        count=removed=0
        for case in prior:
            kernel=build_sector_kernel(bank[case['id']]['triangulation'],case['allowed_types'])
            keep,proof=matching_support(kernel,lambda:None)
            self.assertEqual(keep,case['retained_indices'],(case['id'],case['allowed_types']))
            count+=proof is not None;removed+=len(kernel.support)-len(keep)
        self.assertEqual(len(prior),188);self.assertEqual(count,65);self.assertEqual(removed,126)

    def test_partial_matching_proof_composes_with_complete_Q_support(self):
        raw,_=fixture(3);support=[(0,0),(1,0),(2,0),(3,2),(4,2),(5,0)]
        _,proof=matching_support(build_sector_kernel(raw,support),lambda:None)
        self.assertEqual([s['forced_indices']for s in proof['steps']],[[1],[2]])
        proof['steps']=proof['steps'][:1]
        keep=[0,2,3,4,5]
        intermediate=build_sector_kernel(raw,[support[i]for i in keep])
        result=_discover_in_kernel(intermediate,phase='standard',matching_first=False)
        self.assertEqual(result['status'],'NO_VERTEX_DISC_IN_SECTOR')
        certificate=result['certificate'];self.assertIn('q_support_certificate',certificate)
        certificate['allowed_types']=[list(x)for x in support]
        for entry in certificate['rays']:
            expanded=[0]*len(support)
            for i,value in zip(keep,entry['quadrilaterals']):expanded[i]=value
            entry['quadrilaterals']=expanded
        certificate['matching_support_certificate']=proof
        self.assertTrue(verify_sector_exhaustion(raw,certificate))
        wrong=deepcopy(certificate);wrong['q_support_certificate']['allowed_types']=[list(x)for x in support]
        self.assertFalse(verify_sector_exhaustion(raw,wrong))

    def test_mixed_sign_fixed_point_is_not_a_complete_LP_solver(self):
        # These RREF equations have only the zero nonnegative solution:
        # q2>=2q3 and q3>=2q2. Their sum is strictly positive, but neither
        # individual row is one-sided. Preserve the complete-search fallback.
        rows=((1,0,-1,2),(0,1,2,-1))
        forced,steps=_closure(rows,lambda:None)
        self.assertEqual(forced,set());self.assertEqual(steps,[])
        self.assertEqual(tuple(a+b for a,b in zip(*rows)),(1,1,1,1))

    def test_provenance_mutations_are_rejected_with_producers_disabled(self):
        raw,support=fixture();proof=discover_in_sector(raw,support,phase='standard')['certificate']
        mutations=[]
        for key,value in (('source_sha256','0'*64),('allowed_types',[]),('steps',[])):
            item=deepcopy(proof);item['matching_support_certificate'][key]=value;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['forced_indices'].pop();mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['forced_indices']=[0];mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['row_combination'].pop();mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['row_combination'][0][1]*=-1;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['row_combination'][0][2]=0;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['row_combination'][0][0]=True;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['allowed_types'][0][0]=False;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['steps'][0]['row_combination']*=2;mutations.append(item)
        item=deepcopy(proof);item['matching_support_certificate']['q_support_certificate']={};mutations.append(item)
        item=deepcopy(proof);item['rays'][0]['quadrilaterals'][1]=1;mutations.append(item)
        item=deepcopy(proof);item['rays'].pop();mutations.append(item)
        disabled=('fastunknot.sector_matching_support.matching_support','fastunknot.sector_matching_support._source_constraints',
                  'fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
                  'fastunknot.normal_sector._discover_in_kernel','fastunknot.sector_euler._q_corner_parameters')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
            self.assertTrue(verify_sector_exhaustion(raw,proof))
            for item in mutations:self.assertFalse(verify_sector_exhaustion(raw,item))

    def test_empty_and_all_zero_spaces_and_cooperative_interruption(self):
        self.assertEqual(_kernel_equations((),0,lambda:None),[])
        self.assertEqual(_closure(((1,0),(0,1)),lambda:None)[0],{0,1})
        raw,support=fixture();kernel=build_sector_kernel(raw,support)
        def stop():raise InterruptedError('forcing interrupted')
        with self.assertRaises(InterruptedError):matching_support(kernel,stop)
        # Exact rational implications stay exact rather than rounding signs.
        self.assertEqual(_closure(((Fraction(1,2**90),Fraction(1,3)),),lambda:None)[0],{0,1})


if __name__=='__main__':unittest.main()
