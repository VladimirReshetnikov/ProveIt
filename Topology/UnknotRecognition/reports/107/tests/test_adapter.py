import unittest
from dualforest import solve, from_dense
from integration.native_adapter import from_native_records, native_proposal

class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.counts = {0:{6:1}, 1:{3:1,5:1}, 2:{5:1,7:1,8:1},
                       3:{3:1,6:1,7:1,8:1}, 4:{5:1,6:1,7:1}}
        self.records = [dict(two_handle=r, ends=[None,7] if r<4 else [7,7]) for r in range(5)]

    def test_native_record_translation(self):
        inst, ids = from_native_records(self.counts, [7], self.records)
        result = solve(inst, try_incumbent=False)
        cert = native_proposal(inst, result['certificate'], self.records, ids)
        self.assertEqual(cert['schema'], 'core-three-handle-reduction-v1')
        self.assertEqual(cert['cancellations'], [dict(two_handle=1, three_handle=7)])
        self.assertEqual(cert['surviving_two_handles'], [0,2,3,4])
        self.assertEqual(cert['dual_endpoints'], self.records)

    def test_nonzero_native_root_rejected(self):
        inst = from_dense(2, [(0,1)], [[]], root=1)
        cert = solve(inst)['certificate']
        with self.assertRaises(ValueError):
            native_proposal(inst, cert, [dict(two_handle=0, ends=[None,7])], [7])

    def test_unknown_endpoint(self):
        self.records[0]['ends'][1] = 8
        with self.assertRaises(ValueError):
            from_native_records(self.counts, [7], self.records)

    def test_duplicate_record(self):
        self.records[0]['two_handle'] = 1
        with self.assertRaises(ValueError):
            from_native_records(self.counts, [7], self.records)

    def test_missing_count_row(self):
        del self.counts[2]
        with self.assertRaises(ValueError):
            from_native_records(self.counts, [7], self.records)

if __name__ == '__main__':
    unittest.main()
