"""Weighted least representatives against pointwise connectivity and hostile tags."""
import copy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_transversal import weighted_orbit_transversal
from fastunknot.weighted_transversal_verify import verify_weighted_orbit_transversal


def literal(size, pairs, weights, dimension):
    parent = list(range(size))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for p in pairs:
        for i in range(p.a, p.b+1):
            a, b = root(i), root(p.image(i)); parent[max(a,b)] = min(a,b)
    values = {root(i): [0]*dimension for i in range(size)}
    for lo, hi, value in weights:
        for i in range(lo, hi):
            for j in range(dimension): values[root(i)][j] += value[j]
    return values


class WeightedTransversalTests(unittest.TestCase):
    def checked(self, size, pairs, weights, dimension=2):
        result = weighted_orbit_transversal(size, pairs, weights, dimension=dimension, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        got = {i:r['weight'] for r in result['representative_runs'] for i in range(r['start'],r['stop'])}
        self.assertEqual(got, literal(size,pairs,weights,dimension))
        self.assertTrue(verify_weighted_orbit_transversal(size,pairs,weights,result['certificate'],dimension=dimension))
        return result

    def test_seeded_signed_pairings_and_overlapping_weights(self):
        rng = random.Random(261012)
        for _ in range(750):
            size = rng.randrange(65); pairs=[]; weights=[]
            if size:
                for _ in range(rng.randrange(12)):
                    width=rng.randrange(1,size+1);a=rng.randrange(size-width+1);b=rng.randrange(size-width+1)
                    pairs.append(IntervalPairing(a,a+width-1,b,b+width-1,bool(rng.randrange(2))))
                for _ in range(rng.randrange(12)):
                    lo=rng.randrange(size);hi=rng.randrange(lo+1,size+1)
                    weights.append((lo,hi,[rng.randrange(-8,9),rng.randrange(-8,9)]))
            self.checked(size,pairs,weights)

    def test_weight_swap_with_unchanged_histogram_is_rejected(self):
        weights=[(0,1,[2,3]),(1,2,[5,7])]
        proof=self.checked(2,[],weights)['certificate'];bad=copy.deepcopy(proof)
        a,b=bad['representative_runs'];a['weight'],b['weight']=b['weight'],a['weight']
        self.assertFalse(verify_weighted_orbit_transversal(2,[],weights,bad,dimension=2))
        self.assertEqual(bad['weighted_certificate'],proof['weighted_certificate'])

    def test_huge_binary_orbits_and_independent_replay(self):
        n=1<<16384;pairs=[IntervalPairing(0,n-1,n,2*n-1)];weights=[(0,n,[1,0]),(n,2*n,[0,1])]
        result=weighted_orbit_transversal(2*n,pairs,weights,dimension=2,record_certificate=True)
        self.assertEqual(result['representative_runs'],[dict(start=0,stop=n,weight=[1,1])])
        proof=json.loads(json.dumps(json_safe(result['certificate'])))
        with patch('fastunknot.weighted_transversal._tagged_replay',side_effect=AssertionError('producer used')):
            self.assertTrue(verify_weighted_orbit_transversal(2*n,pairs,weights,proof,dimension=2))

    def test_incomplete_and_callback_contract(self):
        pairs=[IntervalPairing(0,9,10,19)]
        result=weighted_orbit_transversal(20,pairs,[],dimension=2,max_cycles=0,record_certificate=True)
        self.assertEqual(result['status'],'INCONCLUSIVE')
        self.assertNotIn('certificate',result);self.assertNotIn('representative_runs',result)
        proof=self.checked(20,pairs,[])['certificate']
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise ValueError('cancelled')
        with self.assertRaisesRegex(ValueError,'cancelled'):
            weighted_orbit_transversal(20,pairs,[],dimension=2,check=Cancel())
        with self.assertRaisesRegex(ValueError,'cancelled'):
            verify_weighted_orbit_transversal(20,pairs,[],proof,dimension=2,check=Cancel())

if __name__=='__main__':unittest.main()
