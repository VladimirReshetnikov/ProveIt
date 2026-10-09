import copy
from collections import Counter
import random
import unittest
from orbit_transfer import compile_transfer, Circuit, ResourceExhausted, check_trace, InvalidTrace
from orbit_transfer.reference import make_trace, literal_components, eager_histogram, sparse_eager_histogram


def case(rng, n=None):
    n=rng.randrange(1,45) if n is None else n
    rows=[]
    for _ in range(rng.randrange(10)):
        width=rng.randrange(1,n+1)
        a,c=rng.randrange(n-width+1),rng.randrange(n-width+1)
        rows.append((a,a+width-1,c,c+width-1,rng.choice((-1,1))))
    cuts=sorted({0,n}|{rng.randrange(n+1) for _ in range(12)})
    return n,rows,cuts


def literal_profiles(n,rows,cuts):
    return Counter(tuple(sum(a<=x<b for x in orbit) for a,b in zip(cuts,cuts[1:]))
                   for orbit in literal_components(n,rows))


class TransferTests(unittest.TestCase):
    def test_random_full_profiles_both_rules(self):
        rng=random.Random(261008601)
        for _ in range(600):
            n,rows,cuts=case(rng)
            expected=literal_profiles(n,rows,cuts)
            for version in (1,2):
                proof=make_trace(n,rows,version=version)
                prog=compile_transfer(n,rows,proof,cuts)
                actual=Counter()
                for e in prog.emissions:
                    actual[tuple(prog.circuit.transpose([(e.node,1)]))]+=e.multiplicity
                self.assertEqual(actual,expected)
                self.assertEqual(prog.orbit_count,sum(expected.values()))

    def test_random_signed_observables_and_eager_control(self):
        rng=random.Random(261008602)
        for _ in range(200):
            n,rows,cuts=case(rng); proof=make_trace(n,rows)
            prog=compile_transfer(n,rows,proof,cuts)
            d=4; vectors=[tuple(rng.randrange(-9,10) for _ in range(d))
                          for __ in range(len(cuts)-1)]
            intervals=[(a,b,v) for a,b,v in zip(cuts,cuts[1:],vectors)]
            queries=[[(a,b,v[j]) for a,b,v in intervals] for j in range(d)]
            histogram={tuple(x['weight']):x['orbits'] for x in prog.histogram(queries)}
            expected=Counter()
            for orbit in literal_components(n,rows):
                value=[0]*d
                for x in orbit:
                    v=next(v for a,b,v in intervals if a<=x<b)
                    for j in range(d): value[j]+=v[j]
                expected[tuple(value)]+=1
            self.assertEqual(histogram,expected)
            self.assertEqual(eager_histogram(n,rows,proof,intervals,d),expected)

    def test_random_overlapping_ownership_intervals(self):
        rng=random.Random(261008603)
        for _ in range(150):
            n,rows,cuts=case(rng); proof=make_trace(n,rows)
            prog=compile_transfer(n,rows,proof,cuts); owners=[]
            for j in range(9):
                for __ in range(rng.randrange(1,4)):
                    a,b=sorted(rng.sample(cuts,2)); owners.append((j,a,b))
            expected=Counter(tuple(sum(sum(a<=x<b for x in orbit)
                                      for j,a,b in owners if j==q) for q in range(9))
                             for orbit in literal_components(n,rows))
            actual=Counter()
            for i,e in enumerate(prog.emissions): actual[tuple(prog.extract(i,owners,9))]+=e.multiplicity
            self.assertEqual(actual,expected)

    def test_exact_duality(self):
        rng=random.Random(261008604)
        for _ in range(150):
            n,rows,cuts=case(rng); prog=compile_transfer(n,rows,make_trace(n,rows),cuts)
            inp=[rng.randrange(-15,16) for __ in range(len(cuts)-1)]
            seeds=[(e.node,rng.randrange(-7,8)) for e in prog.emissions]
            values=prog.circuit.evaluate(inp); reverse=prog.circuit.transpose(seeds)
            self.assertEqual(sum(values[j]*q for j,q in seeds),sum(a*b for a,b in zip(inp,reverse)))

    def test_huge_translation(self):
        n=2**4096+17; p=37; rows=[(0,n-p-1,p,n-1,1)]
        cuts=[0,11,103,n//2,n-9,n]
        prog=compile_transfer(n,rows,make_trace(n,rows),cuts)
        expected=Counter()
        for residue in range(p):
            expected[tuple((b-1-residue)//p-(a-1-residue)//p for a,b in zip(cuts,cuts[1:]))]+=1
        actual=Counter()
        for e in prog.emissions: actual[tuple(prog.circuit.transpose([(e.node,1)]))]+=e.multiplicity
        self.assertEqual(actual,expected)
        self.assertLess(len(prog.circuit.gates),100)

    def test_huge_reflection(self):
        n=2**4096+1; rows=[(0,n-1,0,n-1,-1)]
        prog=compile_transfer(n,rows,make_trace(n,rows),[0,n])
        self.assertEqual(prog.histogram([[(0,n,1)]]),
                         [{'weight':[1],'orbits':1},{'weight':[2],'orbits':n//2}])

    def test_multiplicity_is_not_witness_scale(self):
        n=2**2048; prog=compile_transfer(n,[],make_trace(n,[]),[0,n])
        self.assertEqual(prog.emissions[0].multiplicity,n)
        self.assertEqual(prog.extract(0,[(0,0,n)],1),[1])
        self.assertEqual(prog.circuit.transpose([(prog.emissions[0].node,n)]),[n])

    def test_numeric_equality_not_source_equality(self):
        prog=compile_transfer(2,[],make_trace(2,[]),[0,1,2])
        self.assertEqual(prog.histogram([[(0,2,0)]]),[{'weight':[0],'orbits':2}])
        self.assertEqual({tuple(prog.extract(i,[(0,0,1),(1,1,2)],2))
                          for i in range(len(prog.emissions))},{(1,0),(0,1)})

    def test_new_endpoint_rejected(self):
        prog=compile_transfer(5,[],make_trace(5,[]),[0,5])
        with self.assertRaises(ValueError): prog.evaluate_intervals([(0,2,1)])
        with self.assertRaises(ValueError): prog.extract(0,[(0,2,5)],1)

    def test_zero_universe(self):
        prog=compile_transfer(0,[],make_trace(0,[]),[])
        self.assertEqual(prog.emissions,())
        self.assertEqual(prog.histogram([[]]),[])

    def test_sharp_threshold_trace(self):
        # Supports below and exactly at p+q-gcd(p,q) = 8 points.
        n=14; rows=[(0,5,4,9,1),(3,7,9,13,1)]
        # second support starts 3: overlap 7, p=4,q=6, threshold 8, so no merge.
        proof=make_trace(n,rows)
        check_trace(n,rows,proof)
        good=[(0,5,4,9,1),(2,7,8,13,1)] # overlap8, sharp threshold8
        proof=make_trace(n,good)
        self.assertTrue(any(e['op']=='merge' for e in proof['operations']))
        proof['version']=1
        with self.assertRaises(InvalidTrace): check_trace(n,good,proof)

    def test_gate_budget_exact_boundary(self):
        n,rows,cuts=case(random.Random(92))
        proof=make_trace(n,rows); count=compile_transfer(n,rows,proof,cuts).stats['circuit_nodes']
        self.assertEqual(compile_transfer(n,rows,proof,cuts,max_nodes=count).stats['circuit_nodes'],count)
        with self.assertRaises(ResourceExhausted): compile_transfer(n,rows,proof,cuts,max_nodes=count-1)
        with self.assertRaises(ValueError): compile_transfer(n,rows,proof,cuts,max_nodes=True)

    def test_cancellation_and_false_callable(self):
        class Stop(Exception): pass
        class Callback:
            def __bool__(self): return False
            def __call__(self): raise Stop()
        with self.assertRaises(Stop): compile_transfer(1,[],make_trace(1,[]),[],check=Callback())

    def test_algebraic_gate_bounds(self):
        rng=random.Random(261008605)
        for _ in range(200):
            n,rows,cuts=case(rng); prog=compile_transfer(n,rows,make_trace(n,rows),cuts)
            mass=prog.circuit.evaluate([1]*(len(cuts)-1))
            self.assertTrue(all(0<=v<=n for v in mass))
            gaps=sum(len(e.get('gaps',())) for e in make_trace(n,rows)['operations'])
            self.assertLessEqual(prog.stats['peak_runs'],len(cuts)-1+4*prog.stats['folds']+2*gaps)
            for e in prog.emissions:
                self.assertLessEqual(sum(prog.circuit.transpose([(e.node,1)])),n)

    def test_sparse_control_against_dense_and_literal(self):
        rng=random.Random(261008609)
        for _ in range(300):
            n,rows,cuts=case(rng); proof=make_trace(n,rows);d=6
            intervals=[]; dense=[]
            for a,b in zip(cuts,cuts[1:]):
                value={j:rng.randrange(-5,6) for j in range(d) if rng.random()<.4}
                intervals.append((a,b,value));dense.append((a,b,[value.get(j,0) for j in range(d)]))
            sparse=sparse_eager_histogram(n,rows,proof,intervals)
            expanded={tuple(dict(key).get(j,0) for j in range(d)):v for key,v in sparse.items()}
            self.assertEqual(expanded,eager_histogram(n,rows,proof,dense,d))

    def test_dense_profile_separation_family(self):
        for d in (4,17,100):
            p=2**100+3; q=2**150; length=q*p+1;n=d*length
            rows=[(0,n-p-1,p,n-1,1)];cuts=[j*length for j in range(d+1)]
            prog=compile_transfer(n,rows,make_trace(n,rows),cuts)
            actual=Counter()
            for e in prog.emissions:
                actual[tuple(prog.circuit.transpose([(e.node,1)]))]+=e.multiplicity
            expected=Counter({tuple(q+int(i==j) for j in range(d)):1 for i in range(d)})
            expected[(q,)*d]=p-d
            self.assertEqual(actual,expected)
            self.assertLess(prog.stats['circuit_nodes'],20*d*(d+1).bit_length())

    def test_source_mass_conservation_coordinatewise(self):
        rng=random.Random(261008610)
        for _ in range(200):
            n,rows,cuts=case(rng);p=compile_transfer(n,rows,make_trace(n,rows),cuts)
            mass=p.circuit.transpose([(e.node,e.multiplicity) for e in p.emissions])
            self.assertEqual(mass,[b-a for a,b in zip(cuts,cuts[1:])])

    def test_callback_during_reverse_and_query(self):
        class Stop(Exception):pass
        def stop():raise Stop()
        p=compile_transfer(3,[],make_trace(3,[]),[0,1,3])
        p.circuit.check=stop
        with self.assertRaises(Stop):p.extract(0,[(0,0,3)],1)
        with self.assertRaises(Stop):p.evaluate_intervals([(0,3,1)])

    def test_invalid_ownership_and_seeds(self):
        p=compile_transfer(3,[],make_trace(3,[]),[0,3])
        with self.assertRaises(ValueError):p.extract(True,[(0,0,3)],1)
        with self.assertRaises(ValueError):p.extract(0,[(1,0,3)],1)
        with self.assertRaises(ValueError):p.extract(0,[(0,-1,3)],1)
        with self.assertRaises(ValueError):p.circuit.transpose([(True,1)])
        with self.assertRaises(ValueError):p.circuit.transpose([(1,True)])

    def test_duplicate_outputs_and_signed_linear_combination(self):
        p=compile_transfer(7,[],make_trace(7,[]),[0,2,7]);a,b=p.emissions
        self.assertEqual(p.circuit.transpose([(a.node,5),(b.node,-3),(a.node,-2)]),[3,-3])

    def test_source_binding_and_incomplete_proof(self):
        n=8;rows=[(0,5,2,7,1)]; p=make_trace(n,rows)
        for name in ('size','orbit_count'):
            q=copy.deepcopy(p);q[name]+=1
            with self.assertRaises(InvalidTrace): check_trace(n,rows,q)
        q=copy.deepcopy(p);q['operations'].pop()
        with self.assertRaises(InvalidTrace): check_trace(n,rows,q)
        with self.assertRaises(InvalidTrace): check_trace(n,[],p)

    def test_bool_rejection(self):
        p=make_trace(1,[])
        for field in ('version','size','orbit_count'):
            q=copy.deepcopy(p);q[field]=True
            with self.assertRaises(InvalidTrace): check_trace(1,[],q)
        with self.assertRaises(InvalidTrace): compile_transfer(1,[],p,[False,1])

    def test_hexadecimal_trace(self):
        n=2**16000+3; p=make_trace(n,[(0,n-2,1,n-1,1)])
        def encode(x):
            if type(x) is int: return hex(x)
            if isinstance(x,list):return [encode(v) for v in x]
            if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
            return x
        prog=compile_transfer(n,[(0,n-2,1,n-1,1)],encode(p),[0,n])
        self.assertEqual(prog.extract(0,[(0,0,n)],1),[n])

    def test_all_rule_types_and_mutations(self):
        rng=random.Random(261008606); witnessed={}
        for _ in range(1000):
            n,rows,cuts=case(rng); p=make_trace(n,rows)
            for j,e in enumerate(p['operations']):
                witnessed.setdefault(e['op'],(n,rows,p,j))
            if len(witnessed)==6:break
        self.assertEqual(set(witnessed),{'delete','trim','merge','transmit','contract','truncate'})
        for op,(n,rows,p,j) in witnessed.items():
            q=copy.deepcopy(p);e=q['operations'][j]
            if op in ('delete','trim','truncate'):e['index']=-1
            elif op=='merge':e['right']=e['left']
            elif op=='transmit':e['target_power']=0
            else:e['gaps'][0][0]+=1
            with self.assertRaises(InvalidTrace):check_trace(n,rows,q)


if __name__=='__main__':unittest.main()
