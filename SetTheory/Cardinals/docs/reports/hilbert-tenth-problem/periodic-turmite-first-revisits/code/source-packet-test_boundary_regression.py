import itertools,random,unittest
from one_visit import *

class TestExact(unittest.TestCase):
    def test_lane_arithmetic(self):
        rng=random.Random(827422)
        for case in range(30000):
            def lane():
                return Lane(tuple(rng.randrange(-6,7) for _ in range(2)),
                            tuple(rng.randrange(-3,4) for _ in range(2)),
                            rng.randrange(15),rng.randrange(1,6),rng.randrange(15))
            a,b=lane(),lane()
            for chronological in (False,True):
                brute_hits=[(a.time(n),n,m) for n in range(a.last+1) for m in range(b.last+1)
                            if a.point(n)==b.point(m) and (not chronological or a.time(n)>b.time(m))]
                expected=min((z[0] for z in brute_hits),default=None)
                hit=collision(a,b,chronological)
                self.assertEqual(expected,None if hit is None else hit[0],(a,b,chronological,hit))
                if hit is not None: self.assertIn(hit,brute_hits)

    def compare(self,rule,tile,defects,start,heading,limit=300):
        exact=decide(rule,tile,defects,start,heading)
        repeat,path=brute(rule,tile,defects,start,heading,limit)
        self.assertEqual(repeat,exact.repeat if exact.repeat is None or exact.repeat[0]<=limit else None,
                         (rule,tile,defects,start,heading,exact))
        end=len(path)
        if exact.repeat is not None: end=min(end,exact.repeat[0]+1)
        for t in range(end): self.assertEqual(path[t],snapshot_head(exact,t))
        self.assertLessEqual(exact.excursions,len(defects)+1)
        return exact

    def test_exhaustive_binary_small(self):
        count=0
        for rule in ('L','R','LL','LR','RL','RR'):
            m=len(rule)
            for u,v in ((1,1),(1,2),(2,1),(2,2)):
                for entries in itertools.product(range(m),repeat=u*v):
                    tile=[entries[y*u:(y+1)*u] for y in range(v)]
                    for heading in range(4):
                        for defect in (None,((0,0),0),((2,-1),m-1)):
                            ds={} if defect is None else {defect[0]:defect[1]}
                            self.compare(rule,tile,ds,(0,0),heading,160); count+=1
        print('exhaustive instances',count)

    def test_random_boards_and_colours(self):
        rng=random.Random(606922); count=0; no_repeat=0
        for case in range(3000):
            m=rng.randrange(1,6); rule=''.join(rng.choice('LR') for _ in range(m))
            u,v=rng.randrange(1,5),rng.randrange(1,5)
            tile=[[rng.randrange(m) for x in range(u)] for y in range(v)]
            ds={(rng.randrange(-8,9),rng.randrange(-8,9)):rng.randrange(m) for _ in range(rng.randrange(8))}
            start=(rng.randrange(-3,4),rng.randrange(-3,4)); heading=rng.randrange(4)
            result=self.compare(rule,tile,ds,start,heading,300)
            no_repeat+=result.repeat is None
            stop=min(100,result.repeat[0] if result.repeat else 100)
            # Independently simulate changing board and compare exact local colours,
            # including time 0, current cell, the first repeated arrival, and m=1.
            board=dict(ds); p=start; h=heading
            for t in range(stop+1):
                for off in ((0,0),(1,0),(0,-1),(-2,1)):
                    q=(p[0]+off[0],p[1]+off[1])
                    self.assertEqual(board.get(q,tile[q[1]%v][q[0]%u]),
                                     colour_at(result,rule,tile,ds,q,t))
                col=board.get(p,tile[p[1]%v][p[0]%u]); board[p]=(col+1)%m
                h=(h+(1 if rule[col]=='R' else -1))%4
                dx,dy=DIRS[h]; p=(p[0]+dx,p[1]+dy)
            count+=1
        print('random instances',count,'certified no revisit',no_repeat)

    def test_huge_defect_jump_and_old_prefix_collision(self):
        n=10**100
        r=decide('RL',[[0,1],[1,0]],{(n,n):1})
        self.assertEqual(r.repeat,(2*n+2,(n-1,n-1),2*n-2))
        self.assertEqual(r.excursions,2)
        self.assertLessEqual(len(r.lanes),8)
        self.assertEqual(snapshot_head(r,2*n),((n,n),0))
        # The repeated arrival has a different heading from the first arrival.
        self.assertNotEqual(snapshot_head(r,2*n+2)[1],snapshot_head(r,2*n-2)[1])
        print('huge jump repeat time',r.repeat[0],'compressed lanes',len(r.lanes))

    def test_unreached_defect_and_zero_drift(self):
        n=10**100
        r=decide('RL',[[0,1],[1,0]],{(-n,n):1})
        self.assertIsNone(r.repeat)
        self.assertEqual(r.tail_drift,(2,2)); self.assertEqual(r.tail_period,4)
        self.assertEqual(snapshot_head(r,2*n),((n,n),0))
        for rule in ('L','R','LL','RR'):
            r=decide(rule,[[0]])
            self.assertEqual(r.repeat[0],4)

    def test_defect_collision_tie(self):
        r=decide('L',[[0]],{(0,0):0})
        self.assertEqual(r.repeat,(4,(0,0),0)); self.assertEqual(r.defects_departed,1)

    def test_query_domain_guard(self):
        r=decide('L',[[0]])
        for t in (-1,5,100):
            with self.assertRaises(ValueError): visited_before(r,(0,0),t)
            with self.assertRaises(ValueError): colour_at(r,'L',[[0]],{},(0,0),t)
        self.assertTrue(visited_before(r,(0,0),4))

    def test_background_permutation(self):
        rng=random.Random(9181)
        for _ in range(1000):
            u,v=rng.randrange(1,9),rng.randrange(1,9)
            turns=[[rng.choice('LR') for x in range(u)] for y in range(v)]
            lanes,tail_start,L,drift=background_excursion(turns,(rng.randrange(-30,30),rng.randrange(-30,30)),rng.randrange(4),19)
            self.assertEqual(tail_start,19)
            self.assertLessEqual(L,4*u*v)
            self.assertEqual(drift[0]%u,0); self.assertEqual(drift[1]%v,0)
            self.assertEqual(len(lanes),L)

if __name__=='__main__': unittest.main(verbosity=2)
