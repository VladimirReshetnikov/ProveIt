import sys
import unittest
from pathlib import Path
from itertools import product
from dataclasses import replace
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from graded_scan import scan,Limits,GObj,Mat,BraidArc,reduce_fifo,check_grading,check_disk,residue_multiplicities
from graded_cube import cube
from block_plan import plan,verify,Piece

class ScannerTests(unittest.TestCase):
    def test_empty_unlink(self):
        for s in range(1,6):
            r=scan(s,[],audit=True); self.assertEqual(r['unreduced_rank'],2**s)
            self.assertEqual(r['verdict'],'UNKNOT' if s==1 else 'LINK')
    def test_known_rank(self):
        self.assertEqual(scan(2,[1]*3)['unreduced_rank'],6)
        self.assertEqual(scan(3,[1,-2]*2)['unreduced_rank'],10)
    def test_small_torus(self):
        for m in range(1,4):
            w=[1,2,3]*m
            self.assertEqual(scan(4,w,audit=True)['bigraded_homology'],cube(4,w)['bigraded_homology'])
    def test_mirror(self):
        w=[1,2,3,1,-2,3,2]
        a=scan(4,w,audit=True); b=scan(4,[-x for x in w],audit=True)
        self.assertEqual(sorted([-h,-q,m] for h,q,m in a['bigraded_homology']),b['bigraded_homology'])
    def test_reducers(self):
        w=[1,2,3]*3+[-2,1]
        results=[scan(4,w,reducer=r,audit=True,record_profiles=True) for r in ('local','rebuild','reverse','reference')]
        for b in results[1:]:
            self.assertEqual(b['bigraded_homology'],results[0]['bigraded_homology'])
            self.assertEqual([t['profile'] for t in b['trace']],[t['profile'] for t in results[0]['trace']])
        for a,b in zip(results[0]['trace'],results[1]['trace']):
            self.assertEqual(a['update_pairs'],b['update_pairs'])
    def test_braid_relation(self):
        for sign in (1,-1):
            a=[sign*x for x in [1,2,1,3,-2,1]]
            b=[sign*x for x in [2,1,2,3,-2,1]]
            self.assertEqual(scan(4,a,audit=True)['bigraded_homology'],scan(4,b,audit=True)['bigraded_homology'])
    def test_far_commutation(self):
        self.assertEqual(scan(4,[1,3,2,1,3])['bigraded_homology'],scan(4,[3,1,2,1,3])['bigraded_homology'])
    def test_inverse_pair(self):
        self.assertEqual(scan(4,[1,2,-2,3])['bigraded_homology'],scan(4,[1,3])['bigraded_homology'])
    def test_markov(self):
        w=[1,-2,1,-2]
        for sign in (1,-1):
            self.assertEqual(scan(3,w)['bigraded_homology'],scan(4,w+[sign*3])['bigraded_homology'])
    def test_invalid(self):
        for s,w in [(0,[]),(4,[0]),(4,[4]),(4,[True]),(4,[1.0])]:
            with self.assertRaises(ValueError): scan(s,w)
    def test_invalid_mode(self):
        with self.assertRaises(ValueError): scan(2,[1],reducer='guess')
    def test_object_limit(self):
        with self.assertRaises(MemoryError): scan(4,[1,2,3],limits=Limits(4,None))
    def test_time_limit(self):
        with self.assertRaises(TimeoutError): scan(4,[1,2,3],limits=Limits(100,1e-12))
    def test_nonzero_radical_not_cancelled(self):
        a=BraidArc(); m=a.intern(((0,1),)); obs=(GObj(m,0,0),GObj(m,1,2))
        d=Mat(obs,obs,[{1:2},{}]); check_grading(d,a,square=True)
        r,stats=reduce_fifo(d,a)
        self.assertEqual(len(r.src),2); self.assertEqual(r.cols[0][1],2)
    def test_guard_false_homogeneity(self):
        a=BraidArc(); m=a.intern(((0,1),)); obs=(GObj(m,0,0),GObj(m,1,0))
        with self.assertRaises(ArithmeticError): check_grading(Mat(obs,obs,[{1:3},{}]),a)
    def test_crossing_pairing_rejected(self):
        a=BraidArc(); m=a.intern(((0,3),(1,2))); obs=(GObj(m,0,0),)
        with self.assertRaises(ArithmeticError): check_disk(Mat(obs,obs,[{}]),a,2)
    def test_sparse_bounds(self):
        r=scan(4,[1,2,3]*5,audit=True)
        for t in r['trace']:
            self.assertLessEqual(t['max_incidence'],9*t['pre_occupancy'])
            self.assertLessEqual(t['queue_pushes'],t['pre_entries']+t['update_pairs'])
            self.assertLessEqual(2*t['pivots'],t['pre_objects'])

class PlannerTests(unittest.TestCase):
    def test_single_block(self):
        r=plan(4,[1,2,3]*10)
        self.assertTrue(any(a['blocks']==1 and a['defects']==0 for a in r))
    def test_mixed(self):
        w=[1,2,3]*4+[-2]+[-3,-2,-1]*3
        r=plan(4,w)
        self.assertTrue(any(a['blocks']==2 and a['defects']==1 for a in r))
        for a in r: self.assertEqual(verify(4,w,a['pieces']),(a['blocks'],a['defects']))
    def test_embedded(self):
        w=[2,3,4]*7+[1]
        self.assertTrue(any(a['blocks']==1 and a['defects']==1 for a in plan(5,w)))
    def test_forged(self):
        w=[1,2,3]*2; a=plan(4,w)[-1]['pieces']
        for b in [replace(a[0],end=5),replace(a[0],pattern=(1,3,2)),replace(a[0],start=1)]:
            with self.assertRaises(ValueError): verify(4,w,[b])
    def test_empty(self):
        r=plan(4,[]); self.assertEqual((r[0]['blocks'],r[0]['defects']),(0,0))
    def test_exhaustive_short(self):
        for n in range(5):
            for w in product((1,2,3),repeat=n):
                for a in plan(4,list(w)): verify(4,list(w),a['pieces'])
    def test_no_false_periodic_block(self):
        self.assertEqual([(a['blocks'],a['defects']) for a in plan(4,[1,-2,3]*2)],[(0,6)])

if __name__=='__main__': unittest.main()
