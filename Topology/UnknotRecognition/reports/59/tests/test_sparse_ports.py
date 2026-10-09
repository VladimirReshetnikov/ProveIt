import copy
import itertools
import random
import types
import sys
import unittest
from unittest.mock import patch
from sparse_ports import (recover, certificate_payload, verify_payload,
                          certificate_queries, ResourceLimit, cone_update,
                          union_relabel)
from sparse_ports.intervals import (IntervalOracle, dense_reference, cone_rows,
                                     selected_union)
from sparse_ports.codec import dumps, loads
from tests.aht_reference import count_orbits, LiteralSystem, periodic_histogram


def zeta_of(hist):
    return lambda u: sum(w for t,w in hist.items() if t & u == t)


class CoreTests(unittest.TestCase):
    def check_histogram(self,r,hist):
        hist={t:w for t,w in hist.items() if w}
        g=zeta_of(hist);total=sum(hist.values())
        for strategy in ('linear','split'):
            found=recover(r,total,g,strategy=strategy)
            self.assertEqual(found.as_dict(),hist)
            self.assertTrue(verify_payload(r,total,certificate_payload(found),g))
            self.assertLessEqual(len(certificate_queries(found)),
                                sum(1+t.bit_count() for t in hist))
        return found

    def test_exhaustive_ternary_histograms(self):
        # 3+9+81+6561 = 6654 separate nonnegative histograms.
        for r in range(4):
            for weights in itertools.product(range(3),repeat=1<<r):
                self.check_histogram(r,dict(enumerate(weights)))

    def test_random_large_weights(self):
        rng=random.Random(261008501)
        for _ in range(1000):
            r=rng.randrange(1,25)
            hist={rng.getrandbits(r):rng.randrange(1,100)*(1<<rng.randrange(100))
                  for _ in range(rng.randrange(1,25))}
            self.check_histogram(r,hist)

    def test_block_query_bound(self):
        # Explicit bound q(T)<=1+2 sum_{ell<h} min(2**ell, |T|).
        rng=random.Random(501)
        for r in (1,2,3,5,16,31,128,1024):
            h=(r-1).bit_length()
            for _ in range(10):
                t=rng.getrandbits(r)
                result=recover(r,7,zeta_of({t:7}))
                bound=1+2*sum(min(1<<ell,t.bit_count()) for ell in range(h))
                self.assertLessEqual(result.oracle_requests,bound)

    def test_empty_and_zero_ports(self):
        self.check_histogram(0,{0:1<<16000})
        self.check_histogram(200,{})
        self.check_histogram(1024,{0:13})

    def test_cert_mutations_and_nonminimal_claim(self):
        hist={0:5,3:2,7:9};g=zeta_of(hist)
        cert=certificate_payload(recover(3,16,g))
        bad=copy.deepcopy(cert);bad['entries'].pop()
        self.assertFalse(verify_payload(3,16,bad,g))
        bad=copy.deepcopy(cert);bad['entries'][0][1]+=1
        self.assertFalse(verify_payload(3,16,bad,g))
        bad=copy.deepcopy(cert);bad['entries'][0][0]=8
        self.assertFalse(verify_payload(3,16,bad,g))
        bad=copy.deepcopy(cert);bad['ports']=True
        self.assertFalse(verify_payload(3,16,bad,g))
        # Matching G({0}) and total is insufficient; the deletion check rejects.
        bad={'version':1,'ports':1,'total':1,'entries':[[1,1]]}
        self.assertFalse(verify_payload(1,1,bad,lambda u:1))
        # Nonnegativity is essential to the proof, not established by samples.
        signed={0:1,1:-1,2:-1,3:2}
        self.assertEqual(sum(signed.values()),1)
        self.assertEqual(zeta_of(signed)(0),1)

    def test_budgets_and_callbacks(self):
        with self.assertRaises(ResourceLimit):
            recover(4,2,zeta_of({1:1,8:1}),max_entries=1)
        with self.assertRaises(ResourceLimit):
            recover(4,1,zeta_of({1:1}),max_requests=0)
        def stop():raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            recover(2,1,lambda u:1,check=stop)
        with self.assertRaisesRegex(RuntimeError,'cancelled'):
            verify_payload(0,0,{},lambda u:0,check=stop)
        for invalid in (True,-1,1.5):
            with self.assertRaises(ValueError):recover(invalid,0,lambda u:0)

    def test_huge_hex_transport(self):
        payload=certificate_payload(recover(16001,1<<16000,
                                            zeta_of({(1<<16000)|1:1<<16000})))
        self.assertEqual(loads(dumps(payload)),payload)
        with self.assertRaises(ValueError):loads('{"$integer":"0x00"}')

    def test_union_relabel(self):
        hist={0:9,1:2,2:3,3:4}
        self.assertEqual(union_relabel(hist.items(),[3]),{0:9,1:9})
        self.assertEqual(union_relabel(hist.items(),[]),{0:18})


class IntervalTests(unittest.TestCase):
    def test_random_interval_graphs(self):
        rng=random.Random(261008502)
        for _ in range(500):
            n=rng.randrange(1,41);rows=[]
            for _ in range(rng.randrange(11)):
                width=rng.randrange(1,n+1)
                a=rng.randrange(n-width+1);c=rng.randrange(n-width+1)
                rows.append((a,a+width-1,c,c+width-1,rng.choice([-1,1])))
            r=rng.randrange(9);ports=[]
            for _ in range(r):
                ports.append([tuple(sorted((rng.randrange(n+1),rng.randrange(n+1))))
                              for _ in range(rng.randrange(4))])
            literal=LiteralSystem(n,rows)
            self.assertEqual(count_orbits(n,rows),literal.count())
            oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,rows+extra))
            result=recover(r,oracle.total,oracle)
            self.assertEqual(result.as_dict(),literal.histogram(ports))
            self.assertEqual(dense_reference(oracle),result.as_dict())
            self.assertTrue(verify_payload(r,oracle.total,certificate_payload(result),oracle))

    def test_cone_continuation_literal(self):
        rng=random.Random(261008503)
        for _ in range(300):
            n=25;r=7
            rows=[(a,a,b,b,1) for a,b in
                  ((rng.randrange(n),rng.randrange(n)) for _ in range(15))]
            ports=[[tuple(sorted((rng.randrange(n+1),rng.randrange(n+1))))]
                   for _ in range(r)]
            system=LiteralSystem(n,rows);hist=system.histogram(ports)
            for _ in range(5):
                selected=rng.getrandbits(r)
                hist=cone_update(hist.items(),selected)
                rows+=cone_rows(selected_union(ports,selected))
                self.assertEqual(hist,LiteralSystem(n,rows).histogram(ports))

    def test_huge_static(self):
        n=1<<16000
        for r in (32,128,1024):
            ports=[[(7,n-9)]]*r
            oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,extra))
            result=recover(r,n,oracle)
            self.assertEqual(result.as_dict(),{0:16,(1<<r)-1:n-16})
            self.assertEqual(oracle.calls,2)

    def test_huge_periodic_analytic(self):
        rng=random.Random(504)
        for bits in (10,100,500,2000):
            period=(1<<bits)+19;n=period*(1<<bits)
            rows=[(0,n-period-1,period,n-1,1)]
            ports=[]
            for _ in range(16):
                lo=rng.randrange(period*2)
                ports.append([(lo,lo+rng.randrange(period//4+1))])
            expected=periodic_histogram(period,ports)
            oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,rows+extra))
            result=recover(len(ports),oracle.total,oracle)
            self.assertEqual(result.as_dict(),expected)
            self.assertEqual(oracle.total,period)

    def test_empty_universe_ports_and_caps(self):
        oracle=IntervalOracle(0,[[],[(0,0)]],lambda extra:count_orbits(0,extra))
        self.assertEqual(recover(2,0,oracle).as_dict(),{})
        with self.assertRaises(ResourceLimit):
            IntervalOracle(5,[],lambda extra:5,max_calls=0)
        with self.assertRaises(ValueError):
            IntervalOracle(5,[[(0,6)]],lambda extra:5)

    def test_general_attachment_counterexample(self):
        # Both systems have two components with the same single-port signature.
        ports=[[(0,4)]]
        first=LiteralSystem(4,[(0,0,1,1,1),(2,2,3,3,1)])
        second=LiteralSystem(4,[(0,0,2,2,1),(1,1,3,3,1)])
        self.assertEqual(first.histogram(ports),second.histogram(ports))
        first.join(0,1);second.join(0,1)
        self.assertNotEqual(first.count(),second.count())


class AdapterContractTests(unittest.TestCase):
    """Adapter ABI tests using independently checked literal count witnesses.

    These are not a run of the maintained AHT trace producer/verifier. The
    injected modules test orchestration, proof binding, budgets and failures.
    """
    def modules(self):
        from tests.aht_reference import Pair
        def row(p):
            return [p.a,p.b,p.c,p.d,-1 if p.reverse else 1] if hasattr(p,'a') else list(p)
        def count(n,pairs,max_cycles=None,check=None,record_certificate=False):
            if check:check()
            if max_cycles is not None and max_cycles<1:
                return types.SimpleNamespace(complete=False,orbits=None,cycles=0)
            rows=[row(p) for p in pairs]
            value=count_orbits(n,rows)
            cert={'size':n,'pairings':rows,'orbit_count':value,'witness':'literal-audit'}
            return types.SimpleNamespace(complete=True,orbits=value,cycles=1,
                                         certificate=cert if record_certificate else None)
        def verify(n,pairs,cert,check=None):
            if check:check()
            return (isinstance(cert,dict) and cert.get('size')==n
                    and cert.get('pairings')==[row(p) for p in pairs]
                    and type(cert.get('orbit_count')) is int
                    and cert['orbit_count']==LiteralSystem(n,[row(p) for p in pairs]).count())
        return {'fastunknot':types.ModuleType('fastunknot'),
                'fastunknot.interval_orbits':types.SimpleNamespace(IntervalPairing=Pair,count_orbits=count),
                'fastunknot.interval_orbit_verify':types.SimpleNamespace(verify_orbit_certificate=verify)}

    def test_adapter_proof_replay_binding_and_budget(self):
        from sparse_ports.proveit import (analyze_port_incidence_sparse as run,
             verify_sparse_port_incidence_certificate as verify)
        from tests.aht_reference import Pair
        with patch.dict(sys.modules,self.modules()):
            pairs=[Pair(0,3,4,7)];ports=[[(0,2)],[(1,3)],[(7,10)],[]]
            result=run(10,pairs,ports,record_certificate=True)
            self.assertEqual(result['status'],'COMPLETE')
            self.assertTrue(verify(10,pairs,ports,result['certificate']))
            self.assertTrue(verify(10,pairs,ports,loads(dumps(result['certificate']))))
            bad=copy.deepcopy(result['certificate']);bad['proofs'][0]['orbit_count']+=1
            self.assertFalse(verify(10,pairs,ports,bad))
            bad=copy.deepcopy(result['certificate']);bad['query_indices'].pop()
            self.assertFalse(verify(10,pairs,ports,bad))
            self.assertFalse(verify(10,pairs,ports[:-1],result['certificate']))
            limited=run(10,pairs,ports,max_cycles=1,record_certificate=True)
            self.assertEqual(limited['status'],'INCONCLUSIVE')
            self.assertNotIn('histogram',limited);self.assertNotIn('certificate',limited)
            # Kill the producer before verification: replay must still work.
            sys.modules['fastunknot.interval_orbits'].count_orbits=lambda *a,**k:1/0
            self.assertTrue(verify(10,pairs,ports,result['certificate']))

    def test_adapter_zero_universe(self):
        from sparse_ports.proveit import (analyze_port_incidence_sparse as run,
             verify_sparse_port_incidence_certificate as verify)
        with patch.dict(sys.modules,self.modules()):
            result=run(0,[],[[],[]],record_certificate=True)
            self.assertTrue(verify(0,[],[[],[]],result['certificate']))


class OrientationTests(unittest.TestCase):
    def test_reflection_fixed_point(self):
        from sparse_ports.orientation import double_cover_rows,lift_ports,refine_double_cover
        signed=[(0,4,0,4,-1,1)];ports=[[(0,5)]]
        base_oracle=IntervalOracle(5,ports,lambda extra:count_orbits(5,[s[:5] for s in signed]+extra))
        base=recover(1,base_oracle.total,base_oracle)
        rows=double_cover_rows(5,signed)
        lifted=IntervalOracle(10,lift_ports(5,ports),lambda extra:count_orbits(10,rows+extra))
        self.assertEqual(refine_double_cover(base,lifted.total,lifted),((1,2,1),))

    def test_random_signed_profiles(self):
        from sparse_ports.orientation import double_cover_rows,lift_ports,refine_double_cover
        rng=random.Random(261008506)
        for _ in range(500):
            n=rng.randrange(1,25);r=rng.randrange(7);signed=[]
            adjacency=[[] for _ in range(n)]
            for _ in range(rng.randrange(9)):
                width=rng.randrange(1,n+1);a=rng.randrange(n-width+1);c=rng.randrange(n-width+1)
                sign=rng.choice([-1,1]);parity=rng.randrange(2)
                b,d=a+width-1,c+width-1;signed.append((a,b,c,d,sign,parity))
                for x in range(a,b+1):
                    y=a+d-x if sign==-1 else x+c-a
                    adjacency[x].append((y,parity));adjacency[y].append((x,parity))
            ports=[[tuple(sorted((rng.randrange(n+1),rng.randrange(n+1))))] for _ in range(r)]
            base_oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,[s[:5] for s in signed]+extra))
            base=recover(r,base_oracle.total,base_oracle)
            cover=double_cover_rows(n,signed)
            lifted=IntervalOracle(2*n,lift_ports(n,ports),lambda extra:count_orbits(2*n,cover+extra))
            answer={t:(a,b) for t,a,b in refine_double_cover(base,lifted.total,lifted)}
            seen={};expected={}
            for root in range(n):
                if root in seen:continue
                seen[root]=0;stack=[root];members=[];consistent=True
                while stack:
                    x=stack.pop();members.append(x)
                    for y,p in adjacency[x]:
                        wanted=seen[x]^p
                        if y in seen:
                            if seen[y]!=wanted:consistent=False
                        else:seen[y]=wanted;stack.append(y)
                mask=0
                for i,port in enumerate(ports):
                    if any(lo<=x<hi for x in members for lo,hi in port):mask|=1<<i
                item=expected.setdefault(mask,[0,0]);item[0 if consistent else 1]+=1
            self.assertEqual(answer,{t:tuple(v) for t,v in expected.items()})

    def test_invalid_cover_does_not_return_result(self):
        from sparse_ports.orientation import refine_double_cover
        base=recover(2,1,zeta_of({1:1}))
        with self.assertRaises(ArithmeticError):refine_double_cover(base,3,lambda u:3)


if __name__ == '__main__':
    unittest.main()
