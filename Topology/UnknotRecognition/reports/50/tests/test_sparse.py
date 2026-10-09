from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from bootstrap import bootstrap
bootstrap()
import copy
import random
import unittest
from unittest.mock import patch
from fastunknot.interval_orbits import IntervalPairing as P, SignedPairing as SP
from fastunknot._sparse_coverage import recover_nonnegative
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as analyze
from fastunknot.sparse_incidence import analyze_sparse_signed_incidence as signed_analyze
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify
from fastunknot.sparse_incidence_verify import verify_sparse_signed_incidence_certificate as signed_verify


def literal(n, pairs, ports, parities=None):
    parent = list(range(n))
    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    adjacency = [[] for _ in range(n)]
    for j, p in enumerate(pairs):
        for x in range(p.a, p.b + 1):
            y = p.image(x)
            parent[root(x)] = root(y)
            e = 0 if parities is None else parities[j]
            adjacency[x].append((y,e)); adjacency[y].append((x,e))
    components = {}
    for x in range(n):
        components.setdefault(root(x), []).append(x)
    hist, signed = {}, {}
    for vertices in components.values():
        mask = 0
        for bit, port in enumerate(ports):
            if any(a <= x < b for a,b in port for x in vertices):
                mask |= 1 << bit
        hist[mask] = hist.get(mask, 0) + 1
        colors, stack, good = {vertices[0]: 0}, [vertices[0]], True
        while stack:
            x = stack.pop()
            for y,e in adjacency[x]:
                if y in colors:
                    if colors[y] != (colors[x] ^ e): good = False
                else:
                    colors[y] = colors[x] ^ e; stack.append(y)
        row = signed.setdefault(mask,[0,0]); row[0 if good else 1] += 1
    return hist, signed


def random_case(rng, n, r, k):
    pairs = []
    for _ in range(k):
        width = rng.randrange(1,n+1)
        a,c = rng.randrange(n-width+1),rng.randrange(n-width+1)
        pairs.append(P(a,a+width-1,c,c+width-1,bool(rng.randrange(2))))
    ports = []
    for _ in range(r):
        port=[]
        for _ in range(rng.randrange(4)):
            a,b=sorted([rng.randrange(n+1),rng.randrange(n+1)])
            port.append((a,b))
        ports.append(port)
    return pairs,ports


class SparseTests(unittest.TestCase):
    def check_case(self,n,pairs,ports):
        expected,_=literal(n,pairs,ports)
        for strategy in ('linear','split'):
            got=analyze(n,pairs,ports,strategy=strategy,record_certificate=True)
            self.assertEqual(got['status'],'COMPLETE')
            self.assertEqual(dict(got['histogram']),expected)
            self.assertTrue(verify(n,pairs,ports,got['certificate']))
        return got

    def test_empty_universe(self): self.check_case(0,[],[[],[]])
    def test_empty_ports(self): self.check_case(9,[],[])
    def test_empty_marks(self): self.check_case(8,[P(0,2,5,7)], [[],[]])
    def test_overlapping_marks(self): self.check_case(8,[],[[(0,4)],[(2,7)],[(2,2)]])
    def test_reflection_midpoint(self): self.check_case(9,[P(0,8,0,8,True)],[[(0,2)],[(4,5)],[(7,9)]])
    def test_singleton_and_identity(self): self.check_case(3,[P(0,0,2,2),P(1,1,1,1,True)],[[(1,2)]])
    def test_random_500(self):
        rng=random.Random(261008901)
        for _ in range(500):
            n=rng.randrange(1,28);r=rng.randrange(9);k=rng.randrange(9)
            self.check_case(n,*random_case(rng,n,r,k))

    def test_arbitrary_nonnegative_1000(self):
        rng=random.Random(261008902)
        for _ in range(1000):
            r=rng.randrange(10)
            h={t:rng.randrange(1,30) for t in rng.sample(range(1<<r),rng.randrange(1,min(30,1<<r)+1))}
            query=lambda u:sum(w for t,w in h.items() if t&u==t)
            for strategy in ('linear','split'):
                got=recover_nonnegative(r,sum(h.values()),query,strategy=strategy)
                self.assertEqual({e['mask']:e['weight'] for e in got['entries']},h)
                if strategy=='linear':
                    self.assertLessEqual(got['stats']['deletion_trials'],r*len(h))

    def test_huge_static(self):
        n=1<<16000
        ports=[[(0,17)],[(30,40)],[(0,17)],[]]
        got=analyze(n,[],ports,record_certificate=True)
        self.assertEqual(dict(got['histogram']),{0:n-27,5:17,2:10})
        self.assertTrue(verify(n,[],ports,got['certificate']))

    def test_128_disjoint_ports(self):
        n=1<<500
        ports=[[(i,i+1)] for i in range(128)]
        got=analyze(n,[],ports,strategy='split',record_certificate=True)
        self.assertEqual(len(got['histogram']),129)
        self.assertTrue(verify(n,[],ports,got['certificate']))

    def test_shared_cycle_limit(self):
        got=analyze(40,[],[[(0,3)],[(5,8)]],max_cycles=1,record_certificate=True)
        self.assertEqual(got['status'],'INCONCLUSIVE')
        self.assertNotIn('histogram',got);self.assertNotIn('certificate',got)
        self.assertEqual(got['stats']['orbit_cycles'],1)

    def test_query_limit(self):
        for q in (0,1,2):
            got=analyze(20,[],[[(0,4)],[(8,11)]],max_queries=q,record_certificate=True)
            self.assertEqual(got['status'],'INCONCLUSIVE')
            self.assertLessEqual(got['stats']['orbit_queries'],q)
            self.assertNotIn('histogram',got)

    def test_signature_limit(self):
        got=analyze(8,[],[[(0,4)]],max_signatures=1,record_certificate=True)
        self.assertEqual(got['status'],'INCONCLUSIVE');self.assertNotIn('certificate',got)

    def test_bad_inputs(self):
        cases=[(True,[],[]),(2,[],[[(0,3)]]),(2,[],[[(False,1)]]),(2,[],[[1]])]
        for args in cases:
            with self.assertRaises(ValueError):analyze(*args)
        with self.assertRaises(ValueError):analyze(2,[],[],max_cycles=True)
        with self.assertRaises(ValueError):analyze(2,[],[],record_certificate=1)
        with self.assertRaises(ValueError):analyze(2,[],[],strategy='bogus')

    def test_callback_propagates(self):
        def fail():raise RuntimeError('cancel')
        with self.assertRaisesRegex(RuntimeError,'cancel'):analyze(4,[],[],check=fail)
        with self.assertRaisesRegex(RuntimeError,'cancel'):verify(4,[],[],{},check=fail)

    def test_independent_replay(self):
        ports=[[(0,2)],[(3,7)]];got=analyze(9,[P(0,1,7,8)],ports,record_certificate=True)
        with patch('fastunknot.interval_orbits.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.sparse_incidence.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.sparse_incidence.recover_nonnegative',side_effect=AssertionError):
            self.assertTrue(verify(9,[P(0,1,7,8)],ports,got['certificate']))

    def test_certificate_mutations(self):
        ports=[[(0,4)],[(2,6)],[(7,9)]]
        cert=analyze(10,[],ports,record_certificate=True)['certificate']
        mutations=[]
        c=copy.deepcopy(cert);c['entries'][0]['weight']+=1;mutations.append(c)
        c=copy.deepcopy(cert);c['entries'].pop();mutations.append(c)
        c=copy.deepcopy(cert);c['entries'].append(c['entries'][0]);mutations.append(c)
        c=copy.deepcopy(cert);c['orbit_count']=True;mutations.append(c)
        c=copy.deepcopy(cert);c['counts']['base']['operations']=[];mutations.append(c)
        c=copy.deepcopy(cert);c['counts']['unions'].pop();mutations.append(c)
        c=copy.deepcopy(cert);c['counts']['unions'].append(c['counts']['unions'][0]);mutations.append(c)
        c=copy.deepcopy(cert)
        e=next(e for e in c['entries'] if e['zeros']);e['zeros'][0][1]=e['mask'];mutations.append(c)
        c=copy.deepcopy(cert);c['entries'][0]['mask']=True;mutations.append(c)
        for c in mutations:self.assertFalse(verify(10,[],ports,c))
        self.assertFalse(verify(11,[],ports,cert))
        self.assertFalse(verify(10,[P(0,0,1,1)],ports,cert))
        self.assertFalse(verify(10,[],ports+[[]],cert))
        for x in (None,[],{},0,True):self.assertFalse(verify(10,[],ports,x))

    def test_known_signed_triangle(self):
        pairs=[P(0,0,1,1),P(1,1,2,2),P(0,0,2,2),P(3,3,4,4)]
        sp=[SP(p,e) for p,e in zip(pairs,[0,0,1,1])]
        ports=[[(0,1)],[(3,4)],[(0,5)]]
        result=signed_analyze(6,sp,ports,record_certificate=True)
        self.assertEqual({m:(a,b) for m,a,b in result['signed_histogram']},{0:(1,0),5:(0,1),6:(1,0)})
        self.assertTrue(signed_verify(6,sp,ports,result['certificate']))
        self.assertLessEqual(result['stats']['cover_orbit_queries'],len(result['histogram'])+1)

    def test_random_signed_300(self):
        rng=random.Random(261008903)
        for _ in range(300):
            n=rng.randrange(1,25);pairs,ports=random_case(rng,n,rng.randrange(8),rng.randrange(8))
            parity=[rng.randrange(2) for p in pairs];sp=[SP(p,e) for p,e in zip(pairs,parity)]
            expected,expected_signed=literal(n,pairs,ports,parity)
            result=signed_analyze(n,sp,ports,strategy='split',record_certificate=True)
            self.assertEqual(dict(result['histogram']),expected)
            self.assertEqual({m:[a,b] for m,a,b in result['signed_histogram']},expected_signed)
            self.assertTrue(signed_verify(n,sp,ports,result['certificate']))
            self.assertLessEqual(result['stats']['cover_orbit_queries'],len(expected)+1)

    def test_signed_empty(self):
        result=signed_analyze(0,[],[[]],record_certificate=True)
        self.assertEqual(result['signed_histogram'],[])
        self.assertTrue(signed_verify(0,[],[[]],result['certificate']))

    def test_signed_budget_and_mutation(self):
        sp=[SP(P(0,9,0,9),1)];ports=[[(0,5)]]
        got=signed_analyze(10,sp,ports,record_certificate=True)
        self.assertTrue(signed_verify(10,sp,ports,got['certificate']))
        for field in ('cover_histogram','signed_histogram'):
            c=copy.deepcopy(got['certificate']);c[field][0][-1]+=1
            self.assertFalse(signed_verify(10,sp,ports,c))
        self.assertFalse(signed_verify(10,[SP(sp[0].pairing,0)],ports,got['certificate']))
        cut=signed_analyze(10,sp,ports,max_queries=got['stats']['orbit_queries']-1,record_certificate=True)
        self.assertEqual(cut['status'],'INCONCLUSIVE');self.assertNotIn('histogram',cut)


if __name__=='__main__':unittest.main()
