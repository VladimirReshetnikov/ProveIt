import random, unittest
from math import lcm
from observations import *
from one_visit import colour_at,brute

class ObservationTests(unittest.TestCase):
    def test_random_boolean_sets(self):
        rng=random.Random(729811)
        for case in range(1000):
            leaves=[]; period=1; cutoff=0
            for _ in range(6):
                lo=rng.randrange(-5,30); hi=rng.choice([None,rng.randrange(-3,45)])
                q=rng.randrange(1,9); r=rng.randrange(-10,11)
                leaves.append((indices(lo,hi,r,q),lambda n,lo=lo,hi=hi,r=r,q=q:
                               n>=0 and n>=lo and (hi is None or n<=hi) and (n-r)%q==0))
                period=lcm(period,q); cutoff=max(cutoff,lo,0 if hi is None else hi+1)
            nodes=leaves[:]
            for _ in range(10):
                a,fa=rng.choice(nodes); b,fb=rng.choice(nodes); op=rng.randrange(3)
                if op==0: nodes.append((a&b,lambda n,fa=fa,fb=fb:fa(n) and fb(n)))
                elif op==1: nodes.append((a|b,lambda n,fa=fa,fb=fb:fa(n) or fb(n)))
                else: nodes.append((~a,lambda n,fa=fa:not fa(n)))
            result,oracle=nodes[-1]
            truth=[n for n in range(cutoff+period) if oracle(n)]
            self.assertEqual(result.minimum(),min(truth,default=None))
            self.assertEqual(result.count(0,cutoff+period-1),len(truth))
            for n in range(50): self.assertEqual(result.contains(n),oracle(n))
        print('random Boolean expressions',1000)

    def test_huge_sets(self):
        M=10**100+39
        self.assertEqual((indices(residue=0,modulus=M)&~indices(0,0)).minimum(),M)
        self.assertEqual((indices(residue=M-1,modulus=M)&indices(residue=M,modulus=M+1)).minimum(),M*(M+1)-1)
        self.assertIsNone((indices(residue=0,modulus=6)&indices(residue=1,modulus=4)).minimum())
        a=indices(10**100,None,3,7)
        self.assertIsNone((a&~a).minimum()); self.assertEqual((a|~a).minimum(),0)
        self.assertEqual(indices(10**100,10**100).minimum(),10**100)
        self.assertIsNone(indices(4,3).minimum()); self.assertEqual(universe().minimum(),0)

    def test_relation_projection(self):
        rng=random.Random(4439)
        for case in range(10000):
            def lane():
                return Lane(tuple(rng.randrange(-8,9) for _ in range(2)),
                            tuple(rng.randrange(-3,4) for _ in range(2)),rng.randrange(-8,20),
                            rng.randrange(1,8),rng.choice([None,rng.randrange(25)]))
            a,b=lane(),lane(); chronological=rng.choice([False,True])
            result=relation_indices(a,b,chronological)
            for n in range(40):
                if a.last is not None and n>a.last: expected=False
                else:
                    point=a.point(n)
                    if b.d==(0,0): k=0 if point==b.p else -1
                    else:
                        dim=0 if b.d[0] else 1; difference=point[dim]-b.p[dim]
                        k=difference//b.d[dim] if difference%b.d[dim]==0 else -1
                    expected=(k>=0 and (b.last is None or k<=b.last) and b.point(k)==point
                              and (not chronological or b.time(k)<a.time(n)))
                self.assertEqual(result.contains(n),expected,(a,b,n,chronological,result.terms))
        print('projected relations',10000,'point checks',400000)

    @staticmethod
    def clause_matches(clause,p,h,board,tile):
        if clause.headings is not None and h not in clause.headings:return False
        if clause.sites is not None and p not in clause.sites:return False
        if any((cx*p[0]+cy*p[1]-r)%q for cx,cy,r,q in clause.congruences):return False
        v,u=len(tile),len(tile[0])
        for dx,dy,c in clause.stencil:
            loc=(p[0]+dx,p[1]+dy)
            if board.get(loc,tile[loc[1]%v][loc[0]%u])!=c:return False
        return True

    def test_random_full_queries(self):
        rng=random.Random(901551); comparisons=0
        for case in range(350):
            m=rng.randrange(1,5); rule=''.join(rng.choice('LR') for _ in range(m))
            u,v=rng.randrange(1,4),rng.randrange(1,4)
            tile=[[rng.randrange(m) for _ in range(u)] for _ in range(v)]
            defects={(rng.randrange(-5,6),rng.randrange(-5,6)):rng.randrange(m) for _ in range(rng.randrange(5))}
            start=(rng.randrange(-2,3),rng.randrange(-2,3)); heading=rng.randrange(4)
            result=decide(rule,tile,defects,start,heading)
            clauses=[]
            for _ in range(rng.randrange(1,4)):
                headings=None if rng.randrange(2) else tuple(rng.sample(range(4),rng.randrange(5)))
                congruences=() if rng.randrange(2) else ((rng.randrange(-2,3),rng.randrange(-2,3),rng.randrange(5),rng.randrange(1,7)),)
                sites=None if rng.randrange(5) else ((rng.randrange(-5,6),rng.randrange(-5,6)),)
                stencil=tuple((rng.randrange(-2,3),rng.randrange(-2,3),rng.randrange(m)) for _ in range(rng.randrange(4)))
                clauses.append(Clause(headings,congruences,sites,stencil))
            hit=first_hit(result,rule,tile,defects,clauses)
            limit=result.repeat[0] if result.repeat else 400
            if hit is not None and hit.time<=10000: limit=max(limit,hit.time)
            board=dict(defects); p=start; h=heading; first=None
            for t in range(limit+1):
                if any(self.clause_matches(c,p,h,board,tile) for c in clauses):first=t;break
                colour=board.get(p,tile[p[1]%v][p[0]%u]);board[p]=(colour+1)%m
                h=(h+(1 if rule[colour]=='R' else -1))%4
                dx,dy=((0,1),(1,0),(0,-1),(-1,0))[h];p=(p[0]+dx,p[1]+dy)
            if first is not None:self.assertIsNotNone(hit);self.assertEqual(hit.time,first)
            else:self.assertTrue(hit is None or hit.time>limit)
            if result.repeat is not None:self.assertEqual(None if hit is None else hit.time,first)
            comparisons+=1
        print('full query instances',comparisons)

    def test_huge_stencil_port(self):
        M=10**100
        clause=Clause(headings=(0,),congruences=((1,0,0,M),),stencil=((0,0,0),(-1,-1,1)))
        result,hit=solve('RL',[[0,1],[1,0]],clauses=(clause,))
        self.assertIsNone(result.repeat);self.assertEqual(hit.time,2*M);self.assertEqual(hit.position,(M,M))
        # An unvisited off-path defect can be seen by the moving finite stencil.
        N=10**100+7
        result,hit=solve('RL',[[0,1],[1,0]],{(N,N+1):0},clauses=(Clause(headings=(0,),stencil=((0,1,0),)),))
        self.assertIsNone(result.repeat);self.assertEqual(hit.time,2*N)
        print('huge stencil first times',2*M,2*N)

    def test_query_endpoints_and_empty_forms(self):
        tile=[[0,1],[1,0]]
        result,hit=solve('RL',tile,clauses=(Clause(),));self.assertEqual(hit.time,0)
        self.assertIsNone(first_hit(result,'RL',tile,{},()))
        self.assertIsNone(first_hit(result,'RL',tile,{},(Clause(headings=()),)))
        self.assertIsNone(first_hit(result,'RL',tile,{},(Clause(sites=()),)))
        self.assertIsNone(first_hit(result,'RL',tile,{},(Clause(stencil=((0,0,0),(0,0,1))),)))
        n=10**50
        result,hit=solve('RL',tile,{(n,n):1},clauses=(Clause(headings=(2,),sites=((n-1,n-1),),stencil=((0,0,1),)),))
        self.assertEqual(hit.time,result.repeat[0]);self.assertEqual(hit.time,2*n+2)
        result,hit=solve('L',[[0]],clauses=(Clause(stencil=((0,0,0),(1,1,0))),));self.assertEqual(hit.time,0)

    def test_one_shot_query_iterables(self):
        tile=[[0,1],[1,0]]; result=decide('RL',tile)
        pairs=[(Clause(stencil=((0,0,1),)),Clause(stencil=iter(((0,0,1),)))),
               (Clause(headings=(1,)),Clause(headings=iter((1,)))),
               (Clause(sites=((1,0),)),Clause(sites=iter(((1,0),)))),
               (Clause(congruences=((1,0,1,7),)),Clause(congruences=iter(((1,0,1,7),))))]
        for a,b in pairs:
            expected=first_hit(result,'RL',tile,{},(a,))
            for _ in range(2):
                self.assertEqual(first_hit(result,'RL',tile,{},(b,)),expected)
        self.assertEqual(first_hit(result,'RL',tile,{},(pairs[0][1],)).time,1)

    def test_validation_survives_optimization(self):
        bad_inputs=[('',[[0]],{},(0,0),0),('X',[[0]],{},(0,0),0),('L',[],{},(0,0),0),
                    ('L',[[0],[0,0]],{},(0,0),0),('L',[[1]],{},(0,0),0),('L',[[0]],{(0,0):1},(0,0),0),
                    ('L',[[0]],{},(0.5,0),0),('L',[[0]],{},(0,0),4)]
        for args in bad_inputs:
            with self.assertRaises(ValueError):decide(*args)
        for q in (0,-1):
            with self.assertRaises(ValueError):indices(modulus=q)
            with self.assertRaises(ValueError):linear_congruence(1,2,q)
        with self.assertRaises(ValueError):IndexSet({atom():2})
        with self.assertRaises(ValueError):relation_indices(Lane((0,0),(1,1),0,0,None),Lane((0,0),(1,1),0,1,None))
        result=decide('L',[[0]])
        for clause in (Clause(headings=(4,)),Clause(congruences=((1,0,0,0),)),Clause(stencil=((0,0,1),))):
            with self.assertRaises(ValueError):first_hit(result,'L',[[0]],{},(clause,))
        for t in (-1,5):
            with self.assertRaises(ValueError):colour_at(result,'L',[[0]],{},(0,0),t)

if __name__=='__main__':unittest.main(verbosity=2)
