import copy
import unittest
from activation_forest import solve
from experiments.fixtures import repository_loop
from integration.records_adapter import from_native_records,native_proposal

class AdapterTests(unittest.TestCase):
    def setUp(self):
        x=repository_loop(); labels=[3,5,6,7,8]
        self.counts={e:{labels[h]:value for h,value in enumerate(row) if value} for e,row in enumerate(x.matrix)}
        self.records=[dict(two_handle=e,ends=[None,37] if e<4 else [37,37]) for e in range(5)]
    def test_normalization(self):
        x,ids,labels=from_native_records(self.counts,[37],self.records)
        self.assertEqual(x,repository_loop()); self.assertEqual(ids,[37]); self.assertEqual(labels,[3,5,6,7,8])
    def test_proposal(self):
        x,ids,_=from_native_records(self.counts,[37],self.records)
        proof=native_proposal(x,solve(x)['certificate'],ids,self.records)
        self.assertEqual(proof['cancellations'],[dict(two_handle=1,three_handle=37)])
        self.assertEqual(proof['surviving_two_handles'],[0,2,3,4])
    def test_mismatched_endpoints(self):
        x,ids,_=from_native_records(self.counts,[37],self.records)
        records=copy.deepcopy(self.records); records[4]['ends']=[None,37]
        with self.assertRaises(ValueError): native_proposal(x,solve(x)['certificate'],ids,records)
    def test_loop_occurrences_kept(self):
        x,_,_=from_native_records(self.counts,[37],self.records)
        self.assertEqual(x.edges[4],(1,1))
    def test_bad_order(self):
        with self.assertRaises(ValueError): from_native_records(self.counts,[37],list(reversed(self.records)))
    def test_signed_count_rejected(self):
        self.counts[0][6]=-1
        with self.assertRaises(ValueError): from_native_records(self.counts,[37],self.records)
    def test_unknown_owner(self):
        self.records[0]['ends'][1]=99
        with self.assertRaises(ValueError): from_native_records(self.counts,[37],self.records)

if __name__=='__main__': unittest.main()
