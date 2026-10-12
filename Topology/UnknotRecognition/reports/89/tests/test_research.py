from __future__ import annotations
import itertools,json,random,sys,unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch
from types import SimpleNamespace
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from moment_kernel import *
from oracles import literal_oracle,block_oracle
from boundary_sources import CircleSource,forget_ports
from group_transport import *
from coning_baseline import compile_coning
from proveit_adapter import make_oracle

COUNTS=Counter()
METRICS={"max_stress_namespace_bits":0,"max_stress_circle_length_bits":0}
RNG=random.Random(20261012)

def normalized(k):
    return (tuple((a,b,int(l>0)) for a,b,l in k.pairs),k.port_owners,k.active_counts,k.passive_counts)

class ResearchTests(unittest.TestCase):
    def test_all_pair_labels(self):
        for m in range(2,66,2):
            for i in range(1,m):
                for j in range(i+1,m+1):
                    # Test an individual discriminant inside a complete matching.
                    rem=[x for x in range(1,m+1) if x not in (i,j)]
                    pairs=[(i,j)]+list(zip(rem[::2],rem[1::2]))
                    hist=[((2,a+b,a*a+b*b,k),1) for k,(a,b) in enumerate(pairs)]
                    expected=tuple(sorted((min(a,b),max(a,b),k) for k,(a,b) in enumerate(pairs)))
                    self.assertEqual(decode_pairs(hist,m),expected);COUNTS['pair_decoder_cases']+=1
    def test_exhaustive_circles(self):
        for n in range(1,11):
            for mask in range(1<<n):
                marks=[(0,j) for j in range(n) if mask>>j&1]
                RNG.shuffle(marks)
                src=CircleSource((n,),tuple(marks),7)
                a=src.compile(block_oracle);b=src.compile(literal_oracle)
                self.assertEqual(a,b);self.assertEqual(a.pairs,src.direct_pairs())
                COUNTS['exhaustive_circle_cases']+=1
    def test_random_multicircles(self):
        for _ in range(700):
            lengths=tuple(RNG.randrange(1,25) for _ in range(RNG.randrange(1,6)))
            marks=[(c,e) for c,n in enumerate(lengths) for e in range(n) if RNG.random()<.35]
            RNG.shuffle(marks);src=CircleSource(lengths,tuple(marks),RNG.randrange(40))
            a=src.compile(block_oracle);self.assertEqual(a,src.compile(literal_oracle))
            self.assertEqual(a.pairs,src.direct_pairs());COUNTS['multicircle_cases']+=1
    def test_exhaustive_coarsening(self):
        for n in range(1,8):
            for states in itertools.product(range(3),repeat=n):
                new=tuple((0,e) for e,s in enumerate(states) if s)
                keep=[j for j,(_,e) in enumerate(new) if states[e]==2]
                RNG.shuffle(keep)
                fine=CircleSource((n,),new).compile(block_oracle)
                coarse=forget_ports(fine,keep)
                direct=CircleSource((n,),tuple(new[j] for j in keep)).compile(block_oracle)
                self.assertEqual(normalized(coarse),normalized(direct))
                self.assertEqual(coarse.pairs,direct.pairs);COUNTS['coarsening_cases']+=1
    def test_block_oracle_arbitrary_weights(self):
        for _ in range(1200):
            size=RNG.randrange(1,90);pairs=[]
            for __ in range(RNG.randrange(15)):
                if size>1 and RNG.random()<.55:
                    a=RNG.randrange(size-1);b=RNG.randrange(a,size-1)
                    pairs.append(Pairing(a,b,a+1,b+1))
                else:
                    a,c=RNG.randrange(size),RNG.randrange(size)
                    pairs.append(Pairing(a,a,c,c,bool(RNG.randrange(2))))
            d=RNG.randrange(1,7);weights=[]
            for __ in range(RNG.randrange(15)):
                a=RNG.randrange(size);b=RNG.randrange(a+1,size+1)
                weights.append((a,b,tuple(RNG.randrange(-7,8) for _ in range(d))))
            self.assertEqual(block_oracle(size,pairs,weights,d),literal_oracle(size,pairs,weights,d))
            COUNTS['block_oracle_cases']+=1
    def test_aliased_corners(self):
        for _ in range(400):
            n=RNG.randrange(1,14);marks=tuple((0,e) for e in range(n) if RNG.random()<.6)
            src=CircleSource((n,),marks,5);size,pairs,term,mass,owners,bc=src.packet()
            # Add disjoint aliases for vertices. Terminal occurrences may choose
            # different aliases while edge mass remains at one canonical endpoint.
            aliases=[RNG.randrange(1,4) for x in range(size)]
            at=size;copies=[]
            for x,k in enumerate(aliases):
                row=[x]
                for __ in range(k):pairs.append(Pairing(x,x,at,at));row.append(at);at+=1
                copies.append(row)
            term=[RNG.choice(copies[x]) for x in term]
            a=compile_kernel(at,pairs,term,mass,owners,bc,block_oracle)
            b=compile_kernel(at,pairs,term,mass,owners,bc,literal_oracle)
            self.assertEqual(a,b);self.assertEqual(a.pairs,src.direct_pairs())
            COUNTS['aliased_corner_cases']+=1
    def test_group_transport(self):
        groups=[cyclic_group(2),symmetric_three()]
        for group in groups:
            g=len(group.table)
            for _ in range(400):
                length=RNG.randrange(0,12);size=length+1;labels=[];expected=group.identity
                for x in range(length):
                    t=RNG.randrange(g);labels.append((Pairing(x,x,x+1,x+1),t));expected=group.mul(expected,t)
                reverse=bool(RNG.randrange(2));term=[length,0] if reverse else [0,length]
                if reverse:expected=group.inv(expected)
                result=transport_census(size,labels,term,[(0,length,1)],group,literal_oracle)
                self.assertEqual(result,((1,2,length,expected),))
                # Noncommutative gauge covariance at every source vertex.
                gauge=[RNG.randrange(g) for x in range(size)]
                changed=[]
                for p,t in labels:
                    u=group.mul(group.mul(group.inv(gauge[p.a]),t),gauge[p.c]);changed.append((p,u))
                transformed=group.mul(group.mul(group.inv(gauge[term[0]]),expected),gauge[term[1]])
                result2=transport_census(size,changed,term,[(0,length,1)],group,literal_oracle)
                self.assertEqual(result2,((1,2,length,transformed),));COUNTS['group_and_gauge_cases']+=1
    def test_group_active_cycle_holonomy(self):
        group=symmetric_three();g=len(group.table)
        for _ in range(350):
            n=RNG.randrange(1,12);ts=[RNG.randrange(g) for _ in range(n)]
            marked=sorted(RNG.sample(range(n),RNG.randrange(1,n+1)))
            src=CircleSource((n,),tuple((0,e) for e in marked));size,_,term,mass,_,_=src.packet()
            labels=[(Pairing(x,x,(x+1)%n,(x+1)%n),ts[x]) for x in range(n) if x not in marked]
            result=transport_census(size,labels,term,mass,group,literal_oracle)
            h=boundary_holonomies(result,[ts[e] for e in marked],group)
            expected=group.identity
            for offset in range(n):expected=group.mul(expected,ts[(marked[0]+offset)%n])
            self.assertEqual(h,((1,expected),));COUNTS['active_holonomy_cases']+=1
    def test_nontrivial_corner_holonomy_rejected(self):
        with self.assertRaises(ValueError):
            transport_census(1,[(Pairing(0,0,0,0),1)],[0,0],[],cyclic_group(2),literal_oracle)
    def test_huge_binary_sources(self):
        for bits in (64,256,1024,4096,16384):
            n=(1<<bits)+33;src=CircleSource((n,1,n+2),((0,0),(0,n//2),(0,n-1),(1,0)),1<<bits)
            METRICS['max_stress_namespace_bits']=max(METRICS['max_stress_namespace_bits'],src.packet()[0].bit_length())
            METRICS['max_stress_circle_length_bits']=max(METRICS['max_stress_circle_length_bits'],max(src.lengths).bit_length())
            got=src.compile(block_oracle);self.assertEqual(got.pairs,src.direct_pairs())
            fine_marks=src.marks+((0,n//3),(2,n//2))
            fine=CircleSource(src.lengths,fine_marks,src.silent_points).compile(block_oracle)
            self.assertEqual(forget_ports(fine,range(4)).pairs,got.pairs)
            COUNTS['huge_binary_cases']+=1
    def test_general_bounded_occupancy(self):
        for bound in (1,2,3,4,5,6):
            for _ in range(100):
                n=RNG.randrange(0,40);ids=list(range(1,n+1));RNG.shuffle(ids);hist=[];expected=[]
                while ids:
                    t=RNG.randrange(1,min(bound,len(ids))+1);row=ids[:t];del ids[:t]
                    hist.append((tuple([t]+[sum(x**k for x in row) for k in range(1,bound+1)]),1));expected.append(tuple(sorted(row)))
                hist.append(((0,)*(bound+1),3))
                self.assertEqual(decode_bounded_moments(hist,n,bound),tuple(sorted(expected)))
                COUNTS['bounded_occupancy_cases']+=1
    def test_two_moment_collision_at_three(self):
        a,b=(1,5,6),(2,3,7)
        self.assertEqual(sum(a),sum(b));self.assertEqual(sum(x*x for x in a),sum(x*x for x in b))
        self.assertNotEqual(sum(x**3 for x in a),sum(x**3 for x in b))
    def test_malformed_profiles(self):
        bad=[ [((2,3,5,0),2)], [((3,6,14,0),1)], [((2,4,8,0),1)],
              [((2,4,9,0),1)], [((2,3,5,-1),1)], [((0,1,0,0),1)],
              [((2,3,5,0),1),((2,3,5,0),1)], [] ]
        for hist in bad:
            with self.assertRaises(ValueError):decode_pairs(hist,2)
            COUNTS['rejected_profile_cases']+=1
    def test_source_contract_errors(self):
        for src in (CircleSource((0,),()),CircleSource((3,),((0,1),(0,1))),CircleSource((3,),((0,3),))):
            with self.assertRaises(ValueError):src.packet()
        with self.assertRaises(ValueError):assemble_kernel(((1,4,1),(2,3,1)),[0,1],[1,1])
        with self.assertRaises(ValueError):assemble_kernel(((1,2,0),),[0],[0])
    def test_resource_semantics(self):
        with self.assertRaises(Incomplete):literal_oracle(200001,[],[],1)
        with self.assertRaises(Incomplete):block_oracle(10,[Pairing(0,4,5,9,True)],[],1)
        def fail(*args):raise Incomplete('intentional')
        with self.assertRaises(Incomplete):CircleSource((3,),((0,0),)).compile(fail)
        self.assertEqual(CircleSource((3,),()).compile(fail).weighted_calls,0)
    def test_count_baseline(self):
        for _ in range(160):
            n=RNG.randrange(1,100);marks=RNG.sample(range(n),RNG.randrange(min(n,14)+1))
            src=CircleSource((n,),tuple((0,e) for e in marks),7)
            got,calls=compile_coning(*src.packet(),block_oracle)
            self.assertEqual(normalized(got),normalized(src.compile(block_oracle)))
            self.assertTrue(calls==0 or calls>=1);COUNTS['coning_comparisons']+=1
    def test_upstream_adapter_contract(self):
        captured={};proofs=[]
        def weighted(size,pairs,weights,**kwargs):
            captured.update(kwargs)
            return {'status':'COMPLETE','certificate':{'schema':'test-only','histogram':[{'weight':[2,3,5,0],'orbits':1}]},'histogram':[{'weight':[999],'orbits':1}]}
        modules={'fastunknot':SimpleNamespace(),'fastunknot.interval_orbits':SimpleNamespace(IntervalPairing=Pairing),
                 'fastunknot.weighted_orbits':SimpleNamespace(weighted_orbit_histogram=weighted),
                 'fastunknot.weighted_orbit_verify':SimpleNamespace(verify_weighted_orbit_certificate=lambda *a,**k:True)}
        with patch.dict(sys.modules,modules):
            call=make_oracle(certificates=proofs,verify=lambda *a:True)
            self.assertEqual(call(1,[],[],4),[((2,3,5,0),1)])
            self.assertTrue(captured['record_certificate']);self.assertEqual(len(proofs),1)
            self.assertEqual(make_oracle()(1,[],[],4),[((2,3,5,0),1)])
            call=make_oracle(verify=lambda *a:False)
            with self.assertRaises(ValueError):call(1,[],[],4)
            modules['fastunknot.weighted_orbits'].weighted_orbit_histogram=lambda *a,**k:{'status':'INCONCLUSIVE'}
            with self.assertRaises(Incomplete):make_oracle()(1,[],[],4)

class AdditionalTests(unittest.TestCase):
    def test_scalar_packing(self):
        for _ in range(800):
            n=RNG.randrange(1,150);marks=RNG.sample(range(n),RNG.randrange(min(n,24)+1))
            src=CircleSource((n,7),tuple((0,e) for e in marks),RNG.randrange(100))
            self.assertEqual(compile_kernel_packed(*src.packet(),block_oracle),src.compile(block_oracle))
            self.assertEqual(compile_kernel_packed(*src.packet(),literal_oracle),src.compile(block_oracle))
            COUNTS['scalar_packing_cases']+=1
    def test_packed_huge(self):
        for bits in (64,1024,16384):
            n=(1<<bits)+7;src=CircleSource((n,),((0,0),(0,1),(0,n-1)),n)
            self.assertEqual(compile_kernel_packed(*src.packet(),block_oracle).pairs,src.direct_pairs())
            json.dumps(kernel_record(compile_kernel_packed(*src.packet(),block_oracle)))
            COUNTS['packed_huge_cases']+=1
    def test_group_coarsening(self):
        group=symmetric_three();g=len(group.table)
        for _ in range(350):
            n=RNG.randrange(1,15);ts=[RNG.randrange(g) for x in range(n)]
            marks=RNG.sample(range(n),RNG.randrange(1,n+1));keep=RNG.sample(range(len(marks)),RNG.randrange(len(marks)+1))
            def get(indices):
                src=CircleSource((n,),tuple((0,e) for e in indices));size,_,term,mass,_,_=src.packet()
                labels=[(Pairing(x,x,(x+1)%n,(x+1)%n),ts[x]) for x in range(n) if x not in indices]
                if not term:return ()
                return transport_census(size,labels,term,mass,group,literal_oracle)
            fine=get(marks)
            self.assertEqual(forget_transport(fine,[ts[e] for e in marks],keep,group),get([marks[j] for j in keep]))
            COUNTS['group_coarsening_cases']+=1
    def test_passive_holonomy_information_barrier(self):
        g=cyclic_group(5)
        weights=[(x,x+1,(x*x+3,)) for x in range(5)]
        hist=[]
        for t in (1,2):
            pairs=[Pairing(x,x,g.mul(x,t),g.mul(x,t)) for x in range(5)]
            hist.append(literal_oracle(5,pairs,weights,1))
        self.assertEqual(hist[0],hist[1])
        self.assertNotEqual(1,2);self.assertNotEqual(g.inv(1),2)
    def test_packed_and_vector_group_agree(self):
        g=symmetric_three()
        for _ in range(200):
            n=RNG.randrange(1,15)
            pairs=[(Pairing(x,x,x+1,x+1),RNG.randrange(6)) for x in range(n)]
            args=(n+1,pairs,[0,n],[(0,n,1)],g,literal_oracle)
            self.assertEqual(transport_census(*args),transport_census(*args,packed=False))
            COUNTS['group_scalar_vector_cases']+=1
    def test_packed_mass_tampering(self):
        src=CircleSource((5,),((0,0),))
        def forged(size,pairs,weights,dimension):
            hist=block_oracle(size,pairs,weights,dimension)
            shift=packing_shift(2)
            return [((w[0]+(1<<(3*shift)),),n) for w,n in hist]
        with self.assertRaises(ValueError):compile_kernel_packed(*src.packet(),forged)

if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromTestCase(ResearchTests),unittest.defaultTestLoader.loadTestsFromTestCase(AdditionalTests)]))
    out={'seed':20261012,'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
         'case_counts':dict(sorted(COUNTS.items())),'stress_metrics':METRICS,
         'scope':'Standalone mathematical/interface validation. No upstream checkout or full unknot recognizer was executed.'}
    (Path(__file__).resolve().parents[1]/'results'/'validation.json').write_text(json.dumps(out,indent=2)+'\n')
    sys.exit(not result.wasSuccessful())
