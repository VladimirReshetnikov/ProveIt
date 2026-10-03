#!/usr/bin/env python3
import copy
import itertools
import json
from fractions import Fraction
from pathlib import Path
import unittest
from certificate import Branch, Machine, Certificate, load_machine, nodup, polynomial

ROOT = Path(__file__).resolve().parent


def guard(op='true', k=0):
    return {'op':'true'} if op == 'true' else {'op':op,'counter':k,'value':0}


def branch(name='edge',source='S',target='H',delta=0,op='true',k=0,tested=None):
    return Branch(name,source,target,k,delta,guard(op,k if tested is None else tested))


def one(delta=0,op='true',k=0,tested=None):
    return Machine(['S','H'],[branch(delta=delta,op=op,k=k,tested=tested)],'S','H',require_reversible=True)


def sample_json():
    instructions = [('S','A',0,'eq'),('A','B',1,'true'),('B','C',0,'gt'),('C','D',-1,'gt'),('D','HALT',0,'true')]
    return dict(schema='reversible-two-counter-v1',controls=['S','A','B','C','D','HALT'],start='S',halt='HALT',class_cut=0,
                branches=[dict(name=f'row{i}',source=s,target=t,side=-1,delta=d,guard=guard(op)) for i,(s,t,d,op) in enumerate(instructions)])


class Tests(unittest.TestCase):
    def test_each_primitive_full_fiber(self):
        # Every coordinate, including inactive offset wires, is enumerated.
        cases = [(0,'true',0),(1,'true',0),(-1,'gt',1),(0,'eq',0),(0,'gt',1),(-1,'gt',0),(0,'eq',1),(0,'gt',0)]
        for delta,op,c0 in cases:
            m=one(delta,op)
            c=Certificate(m,1,'S',(c0,0))
            expected=c.witness()
            found=[w for w in itertools.product(range(3),repeat=c.nvars) if c.evaluate(w)==0]
            self.assertEqual(found,[] if expected is None else [expected])
            r=Certificate(m,1,'S',(c0,0),nonnegative_real=True)
            rational_grid=(0,Fraction(1,2),1,2)
            foundr=[w for w in itertools.product(rational_grid,repeat=r.nvars) if r.evaluate(w)==0]
            self.assertEqual(foundr,[] if expected is None else [expected])

    def test_guard_counter_distinct_from_side(self):
        for op, initial, accepted in [('eq',(9,0),True),('eq',(9,1),False),('gt',(9,1),True),('gt',(9,0),False)]:
            m=one(0,op,k=0,tested=1)
            c=Certificate(m,1,'S',initial)
            w=c.witness()
            self.assertEqual(w is not None,accepted)
            if w is not None:
                self.assertEqual(w[c.offset(0,0)],0)
                self.assertEqual(w[c.offset(0,1)],int(op=='gt'))
                self.assertEqual(w[c.z(0,1)],initial[1]-int(op=='gt'))

    def test_sample_all_rows_and_clock(self):
        m=load_machine(sample_json(),require_reversible=True)
        c=Certificate(m,5,'S',(0,0),clock=True,nonnegative_real=True)
        w=c.witness()
        self.assertIsNotNone(w);self.assertEqual(c.evaluate(w),0)
        self.assertEqual(w[-1],3115)
        self.assertEqual((c.nvars,c.nrows),(46,42))
        for h in (0,1,2,3,4,6,7):
            self.assertIsNone(Certificate(m,h,'S',(0,0)).witness())
        bad=list(w);bad[c.offset(0,1)]=1
        self.assertGreater(c.evaluate(bad),0)

    def test_h_zero(self):
        m=one()
        for real in (False,True):
            for clock in (False,True):
                c=Certificate(m,0,'H',(12,34),clock=clock,nonnegative_real=real)
                self.assertEqual(c.witness(),(0,) if clock else ())
                self.assertEqual((c.nvars,c.nrows),(int(clock),1+int(clock)))
                self.assertIsNone(Certificate(m,0,'S',(0,0),clock=clock,nonnegative_real=real).witness())

    def test_empty_branches_stuck_and_halt(self):
        m=Machine(['S','H'],[],'S','H')
        for h in (1,2):
            c=Certificate(m,h,'S',(0,0))
            self.assertIsNone(c.witness());self.assertGreater(c.evaluate([0]*c.nvars),0)
        self.assertIsNone(Certificate(m,1,'H',(0,0)).witness())
        with self.assertRaises(ValueError):
            Machine(['S','H'],[branch(source='H')],'S','H')

    def test_ledger_matches_materialized(self):
        for data in (sample_json(),dict(schema='reversible-two-counter-v1',controls=['S','H'],start='S',halt='H',class_cut=0,branches=[])):
            m=load_machine(data)
            for h,clock,real,initial in itertools.product(range(4),(False,True),(False,True),((0,0),(2,3))):
                c=Certificate(m,h,'S',initial,clock=clock,nonnegative_real=real)
                rows=c.materialize()['rows'];ledger=c.ledger()
                lengths=[len(t) for _,t in rows]
                self.assertEqual(sum(lengths),ledger['collected_residual_monomials'])
                self.assertEqual(sum(L*L for L in lengths),ledger['expanded_ordered_product_occurrences'])
                self.assertEqual(sum(bool(L) for L in lengths),ledger['nonzero_residuals'])
                self.assertEqual(sum(sum(1 for _ in c.iter_raw_terms(i)) for i in range(c.nrows)),ledger['raw_residual_term_slots'])
                self.assertEqual(len(rows),ledger['squared_residual_slots'])
                self.assertTrue(all(len(mon)<=2 for _,terms in rows for _,mon in terms))

    def test_expanded_polynomial(self):
        m=load_machine(sample_json())
        c=Certificate(m,5,'S',(0,0),clock=True,nonnegative_real=True)
        expanded=c.expanded();w=c.witness()
        self.assertTrue(all(len(mon)<=4 for _,mon in expanded))
        def ev(v):
            return sum(a*__import__('math').prod(v[i] for i in mon) for a,mon in expanded)
        self.assertEqual(ev(w),0)
        for i in range(c.nvars):
            v=list(w);v[i]+=1
            self.assertEqual(ev(v),c.evaluate(v))
            self.assertGreater(ev(v),0)

    def test_exact_domains(self):
        c=Certificate(one(),1,'S',(0,0));w=list(c.witness())
        for x in (True,False,0.0,Fraction(0),-1):
            bad=list(w);bad[0]=x
            with self.assertRaises(ValueError): c.evaluate(bad)
        for h in (True,1.0,Fraction(1),-1):
            with self.assertRaises(ValueError): Certificate(one(),h,'S',(0,0))
        for inp in ((False,0),(0.0,0),(Fraction(0),0),(-1,0)):
            with self.assertRaises(ValueError): Certificate(one(),1,'S',inp)
        r=Certificate(one(),1,'S',(0,0),nonnegative_real=True)
        self.assertEqual(r.evaluate(tuple(Fraction(x) for x in w)),0)
        for x in (True,0.0,-1,Fraction(-1,2)):
            bad=list(w);bad[0]=x
            with self.assertRaises(ValueError): r.evaluate(bad)
        for f in (1,None,'yes'):
            with self.assertRaises(ValueError): Certificate(one(),1,'S',(0,0),clock=f)
        for i in (-1,True,0.0):
            with self.assertRaises(ValueError): c.describe_row(i)
        with self.assertRaises(ValueError): c.evaluate(w+[0])

    def test_branch_public_exact_domains(self):
        b=branch()
        for c in ((True,0),(1.0,0),(Fraction(1),0),(-1,0),(0,),None):
            with self.assertRaises(ValueError): b.enabled(c)
        for flag in (1,0,None,'yes'):
            with self.assertRaises(ValueError): b.mask(flag)
        with self.assertRaises(ValueError): one().kappa(None)

    def test_strict_primitive_schema(self):
        for d,g in [(-1,guard()),(1,guard('gt')),(-1,guard('eq')),(-1,guard('gt',1)),(0,{'op':'gt','counter':0,'value':1}),
                    (0,lambda c: True),(0,True),(0,{'op':'and','args':[]}),(0,{'op':'true','ignored':1}),
                    (0,{'op':'eq','counter':False,'value':0}),(0,{'op':'eq','counter':0,'value':False})]:
            with self.assertRaises(ValueError): Branch('r','S','H',0,d,g)
        for key,value in [('side',True),('delta',True),('name',1)]:
            data=sample_json();data['branches'][0][key]=value
            with self.assertRaises(ValueError): load_machine(data)
        for key,value in [('class_cut',False),('controls',('S','H')),('start',False),('schema',False)]:
            data=sample_json();data[key]=value
            with self.assertRaises(ValueError): load_machine(data)
        with self.assertRaises(ValueError): json.loads('{"x":1,"x":2}',object_pairs_hook=nodup)

    def test_freeze_and_reinitialize(self):
        data=sample_json();m=load_machine(data);c=Certificate(m,5,'S',(0,0))
        data['controls'].clear();data['branches'][0]['guard']['counter']=1
        self.assertIsNotNone(c.witness())
        for target,key,value in ((m,'J',99),(c,'H',1),(m.branches[0],'delta',1)):
            with self.assertRaises((AttributeError,TypeError)): setattr(target,key,value)
            with self.assertRaises((AttributeError,TypeError)): delattr(target,key)
        with self.assertRaises(TypeError): m.codes['S']=3
        with self.assertRaises(TypeError): m.outgoing['S']=()
        for action in (lambda:m.__init__(['H'],[],'H','H'),lambda:c.__init__(m,0,'S',(0,0)),
                       lambda:m.branches[0].__init__('r','S','H',0,0,guard())):
            with self.assertRaises(AttributeError): action()
        self.assertEqual(c.H,5);self.assertEqual(len(m.controls),6)

    def test_determinism_and_optional_injection(self):
        with self.assertRaises(ValueError):
            Machine(['S','H'],[branch('a'),branch('b')],'S','H')
        b=[branch('a',source='A'),branch('b',source='B')]
        m=Machine(['A','S','B','H'],b,'S','H')
        self.assertFalse(m.reversible)
        with self.assertRaises(ValueError): Machine(['A','S','B','H'],b,'S','H',require_reversible=True)
        # Core polynomial over unrestricted nonnegative rational witnesses can
        # average incompatible controls; paid norm removes this spurious zero.
        c=Certificate(m,1,'S',(0,0));r=Certificate(m,1,'S',(0,0),nonnegative_real=True)
        w=(Fraction(1,2),Fraction(1,2),0,0,0,0)
        vals=[]
        for i in range(c.nrows):
            vals.append(sum(a*__import__('math').prod(w[j] for j in mon) for a,mon in c.iter_raw_terms(i)))
        self.assertEqual(sum(v*v for v in vals),0)
        self.assertGreater(r.evaluate(w),0)
        self.assertIsNone(c.witness())

    def test_bounds_reject_without_large_allocations(self):
        c=Certificate(one(),10**12,'S',(0,0),clock=True)
        self.assertEqual(c.nvars,5*10**12+1)
        self.assertEqual(c.ledger()['horizon'],10**12)
        for fn in (c.witness,c.materialize,c.expanded):
            with self.assertRaises(ValueError): fn()
        with self.assertRaises(ValueError): Certificate(one(),1,'S',(0,0)).row(0,max_terms=0)


def make_example():
    data=sample_json();(ROOT/'example-source.json').write_text(json.dumps(data,indent=2)+'\n')
    m=load_machine(data,require_reversible=True)
    c=Certificate(m,5,'S',(0,0),clock=True,nonnegative_real=True)
    out=c.export(ROOT/'example-materialized.json',include_expanded=True)
    w=c.witness()
    (ROOT/'example-witness.json').write_text(json.dumps(w,indent=2)+'\n')
    return dict(variables=c.nvars,squares=c.nrows,degree=max(len(mon) for _,mon in out['expanded_polynomial']),
                distinct_expanded_monomials=len(out['expanded_polynomial']),clock=w[-1],value=c.evaluate(w),ledger=c.ledger())


if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful(): raise SystemExit(1)
    receipt=dict(status='passed',tests=result.testsRun,example=make_example())
    (ROOT/'test-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
