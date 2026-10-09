from __future__ import annotations
import copy,itertools,random,sys,unittest
from collections import deque
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from power_graph import Edge,infer
from graph_checker import verify
from words import inverse,reduce_word,cyclic_reduce,braid_presentation,difference_basis,validate_braid
from donors import extract
from source_checker import decode_donor,verify_braid,_source
from saturation import saturate,probe_braid
from kh_oracle import rank_braid,CubeLimit
from paired_power import family,verify_pair,minor_certificate,verify_minor_certificate
COUNTS={}
def count(key,n=1): COUNTS[key]=COUNTS.get(key,0)+n
def cert(r): return {k:r[k] for k in ('killed','witnesses')}

def valuation_oracle(vertices,edges):
    # Independent prime-valuation vector potentials; no rational arithmetic.
    def factors(x):
        x=abs(x); p=2; out={}
        while p*p<=x:
            while x%p==0: out[p]=out.get(p,0)+1; x//=p
            p+=1
        if x>1: out[x]=out.get(x,0)+1
        return out
    adj={v:[] for v in vertices}
    for e in edges:
        fa,fb=factors(e.a),factors(e.b)
        d={p:fa.get(p,0)-fb.get(p,0) for p in set(fa)|set(fb)}
        s=1 if e.a*e.b>0 else -1
        adj[e.s].append((e.t,d,e.plain,s)); adj[e.t].append((e.s,{p:-v for p,v in d.items()},e.plain,s))
    bad=set(); visited=set()
    for start in vertices:
        if start in visited: continue
        values={start:{}}; q=deque([start]); component=set(); failure=False
        while q:
            v=q.popleft(); component.add(v); visited.add(v)
            for u,d,_,_ in adj[v]:
                wanted={p:values[v].get(p,0)+d.get(p,0) for p in set(values[v])|set(d)}
                wanted={p:a for p,a in wanted.items() if a}
                if u not in values: values[u]=wanted; q.append(u)
                elif values[u]!=wanted: failure=True
        signs={}
        for v in component:
            if v in signs: continue
            signs[v]=1; q=deque([v])
            while q:
                a=q.popleft()
                for b,_,plain,sgn in adj[a]:
                    if not plain: continue
                    s=signs[a]*sgn
                    if b not in signs: signs[b]=s; q.append(b)
                    elif signs[b]!=s: failure=True
        if failure: bad|=component
    return sorted(bad)

def brute_donors(relators):
    # Slow literal oracle, independent of the scanner's LCP/run preprocessing.
    found=set()
    for w in relators:
        R=cyclic_reduce(w)
        if not R: continue
        if len(set(R))==1: found.add((abs(R[0]),abs(R[0]),2,1,True)); continue
        p=next(p for p in range(1,len(R)+1) if len(R)%p==0 and R==R[:p]*(len(R)//p))
        root=R[:p]
        for r in range(p):
            if root[r]==root[r-1]: continue
            u=root[r:]+root[:r]; h=next((j for j in range(1,p) if u[j]!=u[0]),p)
            for k in range((p-h-1)//2+1):
                B=p-h-2*k; W=u[h:h+k]; mid=u[h+k:h+k+B]
                if B and len(set(mid))==1 and (not k or u[-k:]==inverse(W)):
                    found.add((abs(u[0]),abs(mid[0]),h*(1 if u[0]>0 else -1),-B*(1 if mid[0]>0 else -1),k==0))
    return found

def trefoil_nf(word):
    # z=a^2=b^3, followed by alternating syllables of Z_2 * Z_3.
    central=0; stack=[]
    for x in word:
        g=abs(x); power=1 if x>0 else -1; modulus=2 if g==1 else 3
        if stack and stack[-1][0]==g: power+=stack.pop()[1]
        q,r=divmod(power,modulus); central+=q
        if r: stack.append((g,r))
    return central,tuple(stack)

class GraphTests(unittest.TestCase):
    def check(self,vs,es):
        a=infer(vs,es); b=infer(vs,es,modular=False)
        self.assertEqual(a['killed'],b['killed']); self.assertEqual(a['killed'],valuation_oracle(vs,es))
        self.assertTrue(verify(vs,es,cert(a))); self.assertTrue(verify(vs,es,cert(b))); count('graph_oracle_cases')
    def test_single_vertex(self):
        for a,b in itertools.product([-3,-2,-1,1,2,3],repeat=2):
            for p in (False,True): self.check([1],[Edge(1,1,a,b,p)])
    def test_parallel_edges(self):
        options=[Edge(1,2,a,b,p) for a,b in itertools.product([-2,-1,1,2],repeat=2) for p in (False,True)]
        for a,b in itertools.product(options,repeat=2): self.check([1,2],[a,b])
    def test_random_graphs(self):
        rng=random.Random(20517)
        for _ in range(2500):
            vs=list(range(1,rng.randrange(2,18)))
            es=[Edge(rng.choice(vs),rng.choice(vs),rng.choice([-6,-3,-2,-1,1,2,3,6]),rng.choice([-6,-3,-2,-1,1,2,3,6]),rng.choice([False,True])) for _ in range(rng.randrange(45))]
            self.check(vs,es)
    def test_balanced(self):
        rng=random.Random(8402)
        for _ in range(400):
            vs=list(range(1,rng.randrange(3,16))); weight={v:rng.randrange(1,8) for v in vs}; sign={v:rng.choice([-1,1]) for v in vs}; es=[]
            for _ in range(30):
                s,t=rng.sample(vs,2); k=rng.randrange(1,6); p=rng.choice([False,True]); z=sign[s]*sign[t] if p else rng.choice([-1,1])
                es.append(Edge(s,t,k*weight[t],z*k*weight[s],p))
            self.assertEqual(infer(vs,es)['killed'],[]); self.check(vs,es)
    def test_modular_boundaries(self):
        for e in (Edge(1,1,65537,1),Edge(1,1,65538,1),Edge(1,1,65537,65537),Edge(1,1,-1,1,False),Edge(1,1,-1,1,True)):
            a=infer([1],[e]); self.assertEqual(a['killed'],infer([1],[e],modular=False)['killed']); self.assertTrue(verify([1],[e],cert(a))); count('modular_boundary_cases')
    def test_forged_cycles(self):
        vs=[1,2,3,4]; es=[Edge(1,2,2,3),Edge(2,3,5,7),Edge(3,1,11,13),Edge(3,4,1,1)]
        a=cert(infer(vs,es)); self.assertTrue(verify(vs,es,a))
        b=copy.deepcopy(a); b['killed'].remove(4); self.assertFalse(verify(vs,es,b))
        b=copy.deepcopy(a); b['witnesses'][0]['mode']='plain'; self.assertFalse(verify(vs,es,b))
        b=copy.deepcopy(a); b['witnesses'][0]['walk'][0][0]=999; self.assertFalse(verify(vs,es,b))
        b=copy.deepcopy(a); b['witnesses'][0]['walk'][0][1]=True; self.assertFalse(verify(vs,es,b))
        b=copy.deepcopy(a); b['claimed_product']=999; self.assertFalse(verify(vs,es,b)); count('certificate_mutation_rejections',5)
    def test_invalid(self):
        for vs,es in [([True],[]),([1,1],[]),([1],[Edge(1,1,0,1)]),([1],[Edge(1,2,1,1)]),([1],[Edge(1,1,True,1)])]:
            with self.assertRaises(ValueError): infer(vs,es)
    def test_trefoil_inversion(self):
        g=(-1,-2,1,2)
        self.assertNotEqual(trefoil_nf(g),(0,()))
        self.assertEqual(trefoil_nf((-1,)+g+(1,)),trefoil_nf(inverse(g)))
        self.assertEqual(infer([1],[Edge(1,1,1,-1,False)])['killed'],[])
        self.assertEqual(infer([1],[Edge(1,1,1,-1,True)])['killed'],[1])
        for k in range(1,13): self.assertNotEqual(trefoil_nf(g*k),(0,()))
        count('trefoil_normal_form_checks',15)
    def test_not_all_torsionfree_groups(self):
        def mul(f,g): return f[0]*g[0],f[0]*g[1]+f[1]
        x=(Fraction(1),Fraction(1)); w=(Fraction(1,2),Fraction(0)); wi=(Fraction(2),Fraction(0))
        self.assertEqual(mul(mul(w,mul(x,x)),wi),x); self.assertNotEqual(x,(1,0))

class DonorTests(unittest.TestCase):
    def test_exhaustive_short_words(self):
        for n in range(1,7):
            for w in itertools.product([-2,-1,1,2],repeat=n):
                es,ps=extract([w]); self.assertEqual({(e.s,e.t,e.a,e.b,e.plain) for e in es},brute_donors([w]))
                self.assertEqual(es,[decode_donor([w],p) for p in ps]); count('literal_donor_oracles')
    def test_constructed_donors(self):
        rng=random.Random(1008)
        for _ in range(1000):
            s,t=rng.sample([1,2,3,4],2); a=rng.randrange(1,5)*rng.choice([-1,1]); b=rng.randrange(1,5)*rng.choice([-1,1])
            W=reduce_word(rng.choices([-4,-3,-2,-1,1,2,3,4],k=rng.randrange(7)))
            word=((s if a>0 else -s,)*abs(a)+W+(t if b<0 else -t,)*abs(b)+inverse(W))*rng.randrange(1,5)
            es,ps=extract([word]); self.assertEqual(es,[decode_donor([word],p) for p in ps]); self.assertEqual({(e.s,e.t,e.a,e.b,e.plain) for e in es},brute_donors([word])); count('constructed_donor_oracles')
    def test_donor_forgery(self):
        roots=[(1,1,3,-2,-2,-2,-3)]; es,ps=extract(roots); self.assertTrue(es)
        for p in ps:
            for key,value in [('period',10**40),('rotation',True),('conj',1000),('slot',5)]:
                q=copy.deepcopy(p); q[key]=value
                with self.assertRaises(ValueError): decode_donor(roots,q)
                count('donor_mutation_rejections')
    def test_closure(self):
        roots=[(1,1,-2,-2,-2),(1,1,1,1,1,-2,-2,-2,-2,-2,-2,-2),(2,3,-4,-3)]
        final,alive,rounds,counts=saturate(roots,[1,2,3,4])
        self.assertEqual(alive,[3]); self.assertTrue(all(not w for w in final))
        self.assertTrue(all(counts[i+1]['letters']<=counts[i]['letters'] for i in range(len(counts)-1)))

class PairTests(unittest.TestCase):
    def test_no_unit_minor_needed(self):
        rows=[(1,2,2,3),(1,2,4,9),(1,2,5,4)]
        p=minor_certificate(rows);self.assertIsNotNone(p);self.assertTrue(verify_minor_certificate(rows,p))
        self.assertTrue(all(abs(rows[i][2]*rows[j][3]-rows[i][3]*rows[j][2])!=1 for i in range(3) for j in range(i)))
        self.assertFalse(verify_minor_certificate(rows,{'minors':[[0,1]],'vertices':[1,2]}))
        self.assertTrue(verify_minor_certificate([rows[0],list(rows[1]),rows[2]],p));count('minor_block_checks',4)
    def test_random_minor_blocks(self):
        from math import gcd
        rng=random.Random(746)
        for _ in range(200):
            rows=[(1,2,rng.randrange(1,30),rng.randrange(1,30)) for k in range(rng.randrange(2,10))]
            g=0
            for i in range(len(rows)):
                for j in range(i):g=gcd(g,rows[i][2]*rows[j][3]-rows[i][3]*rows[j][2])
            p=minor_certificate(rows);self.assertEqual(p is not None,g==1)
            if p:self.assertTrue(verify_minor_certificate(rows,p))
            count('random_minor_blocks')

    def test_large_unit_determinants(self):
        for bits in [1,16,128,1024,16384]:
            rows,proofs=family(4,bits)
            self.assertTrue(all(verify_pair(rows,p) for p in proofs))
            es=[Edge(s,t,a,b,True) for s,t,a,b in rows]
            self.assertEqual(infer(list(range(1,10)),es)['killed'],list(range(1,9)))
            count('binary_unit_pair_checks',4)
    def test_unit_pair_forgery(self):
        rows,proofs=family(1,8)
        wrong=[rows[0],(1,2,258,259)]
        self.assertFalse(verify_pair(wrong,proofs[0]))
        p=copy.deepcopy(proofs[0]);p['vertices']=[True,2]
        self.assertFalse(verify_pair(rows,p));count('unit_pair_mutations',2)

class SourceTests(unittest.TestCase):
    def test_source_conventions(self):
        rng=random.Random(4127)
        for _ in range(500):
            n=rng.randrange(2,6); b=[rng.choice([-1,1])*rng.randrange(1,n) for _ in range(rng.randrange(10))]
            try: validate_braid(n,b)
            except ValueError: continue
            a=difference_basis(braid_presentation(n,b),n); self.assertEqual(a,[tuple(w) for w in _source(n,b,200000)])
            es,ps=extract(a); self.assertEqual(es,[decode_donor(a,p) for p in ps]); count('source_convention_comparisons')
    def test_positives(self):
        for n,b in [(1,[]),(2,[1]),(2,[-1]),(3,[1,2]),(3,[1,-2]),(3,[1,2,1,-2]),(4,[1,2,3])]:
            out=probe_braid(n,b); self.assertEqual(out['status'],'UNKNOT'); self.assertTrue(verify_braid(n,b,out['certificate'])); count('source_positive_examples')
    def test_source_forgery(self):
        p=probe_braid(2,[1])['certificate']; self.assertFalse(verify_braid(2,[1,1,1],p))
        q=copy.deepcopy(p); q['rounds'][0]['graph']['killed']=[2]; self.assertFalse(verify_braid(2,[1],q))
        q=copy.deepcopy(p); q['rounds'][0]['donors'][0]['slot']=True; self.assertFalse(verify_braid(2,[1],q))
        q=copy.deepcopy(p); q['version']=True; self.assertFalse(verify_braid(2,[1],q)); count('source_forgery_rejections',4)
    def test_resource_limits(self):
        self.assertEqual(probe_braid(2,[1]*9,letter_cap=5)['status'],'RESOURCE_LIMIT')
        with self.assertRaises(ValueError): probe_braid(3,[1])
        with self.assertRaises(CubeLimit): rank_braid(2,[1]*11)

class HomologyTests(unittest.TestCase):
    def test_known_values(self):
        for n,b,rank in [(1,[],1),(2,[1],1),(2,[1]*3,3),(2,[-1]*3,3),(2,[1]*5,5),(3,[1,-2]*2,5),(3,[1,2]*4,5)]:
            self.assertEqual(rank_braid(n,b)['rank'],rank); count('known_homology_values')
    def test_markov_and_inverse(self):
        rng=random.Random(2451)
        for _ in range(36):
            n=rng.choice([2,3]); b=[rng.choice([-1,1])*rng.randrange(1,n) for _ in range(rng.randrange(1,5))]
            try: validate_braid(n,b)
            except ValueError: continue
            r=rank_braid(n,b)['rank']
            for sign in [-1,1]: self.assertEqual(rank_braid(n+1,b+[sign*n])['rank'],r); count('markov_rank_comparisons')
            c=rng.randrange(1,n); self.assertEqual(rank_braid(n,b+[c,-c])['rank'],r); count('inverse_pair_rank_comparisons')
            self.assertEqual(rank_braid(n,[-x for x in b])['rank'],r); count('mirror_rank_comparisons')
    def test_random_probe_vs_homology(self):
        rng=random.Random(99310); done=0
        while done<180:
            n=rng.choice([2,3,4]); b=[rng.choice([-1,1])*rng.randrange(1,n) for _ in range(rng.randrange(1,9))]
            try: validate_braid(n,b)
            except ValueError: continue
            kh=rank_braid(n,b); p=probe_braid(n,b)
            if p['status']=='UNKNOT': self.assertEqual(kh['rank'],1); self.assertTrue(verify_braid(n,b,p['certificate']))
            done+=1; count('random_braid_homology_comparisons')

if __name__=='__main__': unittest.main(verbosity=2)
