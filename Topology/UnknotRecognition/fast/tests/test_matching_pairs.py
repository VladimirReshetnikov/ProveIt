"""Two-row matching implications keep source geometry and fallback authority."""
from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import build_sector_kernel,discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion,_matching_support_indices,_digest
from fastunknot.sector_matching_support import _closure,_combined_closure,_pair_step,matching_support
from fastunknot.normal_surface_geometry import _prepare

ROOT=Path(__file__).resolve().parents[2]

class MatchingPairTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank={r['id']:r for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']}
        cls.hits=json.loads((ROOT/'synthesis/data/matching-pair-pilot.json').read_text())['hits']

    def test_mixed_pair_forces_zeros_and_exact_interval_cases(self):
        rows=((1,0,-1,2),(0,1,2,-1))
        self.assertEqual(_closure(rows,lambda:None)[0],set())
        self.assertEqual(_combined_closure(rows,lambda:None)[0],set(range(4)))
        step=_pair_step(((1,-1,0),(-1,1,1)),set(),lambda:None)
        self.assertEqual(step,([(0,Fraction(1)),(1,Fraction(1))],[2]))
        step=_pair_step(((1,-2,0),(0,1,1)),set(),lambda:None)
        self.assertEqual(step[0],[(0,Fraction(1)),(1,Fraction(3))])
        self.assertEqual(step[1],[0,1,2])
        self.assertIsNone(_pair_step(((1,-1),(-1,1)),set(),lambda:None))

    def test_three_row_counterexample_preserves_incompleteness(self):
        rows=((1,0,0,-2,1,1),(0,1,0,1,-2,1),(0,0,1,1,1,-2))
        self.assertEqual(_combined_closure(rows,lambda:None),(set(),[]))
        self.assertEqual(tuple(sum(col)for col in zip(*rows)),(1,1,1,0,0,0))
        # The all-three-row consequence forces the pivot coordinates to zero.
        # A positive free-coordinate vector still solves the system.
        self.assertTrue(all(sum(a*b for a,b in zip(row,(0,0,0,1,1,1)))==0 for row in rows))

    def test_fifty_actual_source_implications_replay_without_producers(self):
        self.assertEqual(len(self.hits),50)
        for hit in self.hits:
            raw=self.bank[hit['id']]['triangulation'];kernel=build_sector_kernel(raw,hit['support'])
            keep,proof=matching_support(kernel,lambda:None)
            self.assertEqual(keep,[i for i in range(len(hit['support']))if i not in hit['new_forced']])
            with patch('fastunknot.sector_matching_support._source_constraints',side_effect=AssertionError('producer')):
                retained=_matching_support_indices(_prepare(raw,lambda:None),list(kernel.support),proof,_digest(raw),lambda:None)
            self.assertEqual(retained,keep)

    def test_high_nullity_real_source_uses_planar_search_and_complete_legacy_replay(self):
        for hit in (h for h in self.hits if h['raw_nullity']>3):
            raw=self.bank[hit['id']]['triangulation']
            result=discover_in_sector(raw,hit['support'],phase='standard',max_bases=7)
            self.assertEqual(result['status'],'NO_VERTEX_DISC_IN_SECTOR')
            self.assertEqual(result['stats']['matching_nullity'],3)
            self.assertEqual(result['stats']['method'],'planar-adaptive')
            self.assertEqual(result['stats']['bases_attempted'],7)
            proof=result['certificate']
            disabled=('fastunknot.sector_matching_support.matching_support',
                'fastunknot.sector_matching_support._pair_step','fastunknot.normal_sector.build_sector_kernel',
                'fastunknot.normal_sector.sector_rays','fastunknot.sector_planar.sector_planar_rays')
            with ExitStack()as stack:
                for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer')))
                self.assertTrue(verify_sector_exhaustion(raw,proof))
                legacy=deepcopy(proof);legacy.pop('matching_support_certificate')
                self.assertTrue(verify_sector_exhaustion(raw,legacy))
                changed=deepcopy(proof)
                changed['matching_support_certificate']['steps'][-1]['row_combination'][0][1]+=1
                self.assertFalse(verify_sector_exhaustion(raw,changed))

    def test_shared_candidate_cap_and_cancellation(self):
        hit=next(h for h in self.hits if h['raw_nullity']>3)
        raw=self.bank[hit['id']]['triangulation']
        result=discover_in_sector(raw,hit['support'],phase='standard',max_bases=6)
        self.assertEqual(result['status'],'INCONCLUSIVE');self.assertNotIn('certificate',result)
        def stop():raise InterruptedError('pair bounds cancelled')
        with self.assertRaises(InterruptedError):_pair_step(((1,-1),(-1,2)),set(),stop)
        with self.assertRaises(InterruptedError):matching_support(build_sector_kernel(raw,hit['support']),stop)

    def test_large_rational_interval_is_exact(self):
        n=1<<8192
        rows=((Fraction(1),Fraction(-n),Fraction(0)),
              (Fraction(-1,2*n),Fraction(1),Fraction(1)))
        coefficients,added=_pair_step(rows,set(),lambda:None)
        vector=[sum(scale*rows[index][j]for index,scale in coefficients)for j in range(3)]
        self.assertTrue(all(x>=0 for x in vector))
        self.assertEqual(added,[i for i,x in enumerate(vector)if x>0])
        self.assertTrue(added)
        self.assertTrue(all(isinstance(scale,Fraction)for _,scale in coefficients))

if __name__=='__main__':unittest.main()
