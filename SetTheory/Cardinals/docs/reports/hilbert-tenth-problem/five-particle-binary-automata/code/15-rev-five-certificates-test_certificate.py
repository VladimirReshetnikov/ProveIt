"""Standard-library exact regression and tiny complete-fiber enumerations."""
from certificate import Branch, Machine, Certificate, load_machine, guard_value
from fractions import Fraction
from dataclasses import FrozenInstanceError
from itertools import product
from pathlib import Path
import copy
import json

checks = {}
def check(label, condition):
    if not condition:
        raise AssertionError(label)
    checks[label] = checks.get(label,0)+1

def rejects(label,fn):
    try:
        fn()
    except (ValueError,AttributeError,FrozenInstanceError):
        checks[label] = checks.get(label,0)+1
        return
    raise AssertionError('accepted invalid request: '+label)

def make(guard=True,delta=0,counter=0,J=1):
    return Machine(['A','H'],[Branch('b','A','H',counter,delta,guard)],'H',J)

def check_certificate(f, expected):
    w = f.witness()
    check('acceptance', (w is not None) == expected)
    B,r,H = len(f.machine.cells),f.ledger()['tail_occurrences'],f.H
    check('variable ledger',len(f.names) == H*(B+2+r)+int(f.clock))
    check('residual ledger',len(f.residuals) == H*(4+2*B+int(f.real))+1+int(f.clock))
    check('degree ledger',f.ledger()['degree_upper_bound'] <= 4)
    if H:
        P=f.ledger()['normalized_nonzero_branches']
        bound=H*(7*B+P+r+5)+2+int(f.real)*H*(B+1)+int(f.clock)*(1+H*(B+P))
        check('raw slot upper bound',f.ledger()['residual_monomial_occurrences'] <= bound)
    if w is None:
        return
    check('zero residuals',f.evaluate(w)==0)
    check('height',max(w,default=0) <= max(1,f.ledger()['counter_and_slack_height'],f.ledger()['clock_height']))
    for i in range(len(w)):
        bad = list(w)
        bad[i] += 1
        check('single-coordinate mutations rejected',f.evaluate(bad)>0)
    expanded = f.expanded()
    for delta in (0,1):
        test = tuple(v+delta for v in w)
        value=0
        for a,mon in expanded:
            for i in mon:
                a *= test[i]
            value += a
        check('exact expanded identity',value==f.evaluate(test))

# True guard sample must match the compiler's literal JSON and clock.
sample,start=load_machine(json.loads(Path('sample-source.json').read_text()))
for real in (False,True):
    f=Certificate(sample,1,start,(0,0),clock=True,nonnegative_real=real)
    check_certificate(f,True)
    check('sample clock696',f.witness()[f.theta]==696)
    check('sample geometry',f.machine.geometry()==dict(m=2,p=1,a=0,J=1,D=8,S=18,Z=382))
    f.export('sample-real-certificate.json' if real else 'sample-certificate.json')
    Path('sample-real-witness.json' if real else 'sample-witness.json').write_text(json.dumps(f.witness())+'\n')
check_certificate(Certificate(sample,2,start,(0,0)),False)
check_certificate(Certificate(sample,0,start,(0,0)),False)
for clock,real in product((False,True),repeat=2):
    f=Certificate(sample,0,'HALT',(2,3),clock=clock,nonnegative_real=real)
    check_certificate(f,True)
    check('h0 dimensions',len(f.names)==int(clock) and len(f.residuals)==1+int(clock))
    check_certificate(Certificate(sample,1,'HALT',(2,3),clock=clock,nonnegative_real=real),False)

# Boundary cases and both tails, including guards on the untouched counter.
for delta,counter in product((-1,0,1),(0,1)):
    G=('and',('gt',counter,0),('or',('eq',1-counter,2),('gt',1-counter,2)))
    m=make(G,delta,counter,J=3)
    for c in product(range(7),repeat=2):
        for real in (False,True):
            f=Certificate(m,1,'A',c,clock=True,nonnegative_real=real)
            check_certificate(f,guard_value(m.branches[0].guard,c))
            if f.witness() is not None:
                b=next(i for i,e in enumerate(f.selectors[0]) if f.witness()[e])
                for k,s in enumerate(f.slacks[0][b]):
                    if s is not None:
                        check('tail exact value',f.witness()[s]==c[k]-4)
# Both sides of J / J+1, direct guards independent of selected updated counter.
m=make(('or',('eq',1,3),('gt',1,3)),1,0,J=3)
for y in (2,3,4,5):
    check_certificate(Certificate(m,1,'A',(5,y),clock=True),y>=3)

# Logical DNF overlap is normalized once; impossible branches produce no cells.
m=make(('or',('eq',0,0),('eq',0,0)),0,0,J=1)
check('DNF duplicate merged by cells',len(m.cells)==3)
check_certificate(Certificate(m,1,'A',(0,8)),True)
impossible=make(('and',('eq',0,0),('gt',0,0)),0,0,J=1)
check('impossible normalization',not impossible.cells)
check_certificate(Certificate(impossible,1,'A',(0,0)),False)
empty=Machine(['A','H'],[],'H',0)
check_certificate(Certificate(empty,1,'A',(0,0)),False)

# A partial-injective multistep chain; early halt and stuck traces cannot pad.
chain=Machine(['A','B','H'],[
    Branch('inc','A','B',0,1,True),
    Branch('dec','B','H',1,-1,('gt',1,0))], 'H',1)
for H in (0,1,2,3):
    check_certificate(Certificate(chain,H,'A',(0,2),clock=True),H==2)
    check_certificate(Certificate(chain,H,'A',(0,0),clock=True),False)

# Exact complete fibers for tiny systems (all coordinates enumerated).
fibers=[]
for G,c,J,expected in [
    (('and',('eq',0,0),('eq',1,0)),(0,0),0,True),
    (('and',('eq',0,0),('eq',1,0)),(1,0),0,False),
    (('and',('gt',0,0),('gt',1,0)),(1,1),0,True),
    (('or',('and',('eq',0,0),('eq',1,0)),('and',('gt',0,0),('gt',1,0))),(1,1),0,True)]:
    f=Certificate(make(G,0,0,J),1,'A',c)
    zeros=[w for w in product(range(3),repeat=len(f.names)) if f.evaluate(w)==0]
    check('complete bounded fiber',zeros==([f.witness()] if expected else []))
    fibers.append(dict(variables=len(f.names),domain_values=[0,1,2],tuples=3**len(f.names),zeros=len(zeros)))

# Real norm is necessary in general even with a reversible source.
# MID has no exits. A 1/2 convex mixture of L and R branches spoofs its state code.
real_source=Machine(['L','MID','R','H'],[
    Branch('up','L','H',0,1,('and',('eq',0,0),('eq',1,0))),
    Branch('same','R','H',0,0,('and',('eq',0,0),('eq',1,0)))],'H',1)
f=Certificate(real_source,1,'MID',(0,0),nonnegative_real=True)
w=[Fraction(1,2),Fraction(1,2),Fraction(1,2),0]
vals=dict(f.residual_values(w))
check('fractional convex mixture fools unpaid residuals',all(v==0 for label,v in vals.items() if not label.endswith('.norm')))
check('paid norm rejects convex mixture',vals['0.norm']==Fraction(-1,2) and f.evaluate(w)>0)
check('natural stuck state has no witness',f.witness() is None)

# Exact all-input source checks: domains, images, naturalness, syntax and cutoff.
rejects('overlapping source domains',lambda:Machine(['A','H'],[Branch('x','A','H',0,0,True),Branch('y','A','H',0,0,True)],'H',1))
rejects('overlapping source images',lambda:Machine(['A','B','H'],[Branch('x','A','H',0,0,True),Branch('y','B','H',0,1,True)],'H',1))
rejects('negative output allowed',lambda:make(True,-1,0,1))
rejects('image cutoff insufficient',lambda:make(('eq',0,1),1,0,1))
rejects('domain cutoff insufficient',lambda:make(('gt',1,2),0,0,1))
rejects('outgoing halt',lambda:Machine(['A','H'],[Branch('x','H','A',0,0,True)],'H',1))
for bad in (True,1.0,-1,Fraction(1,1)):
    rejects('counter domain exact',lambda bad=bad:Certificate(sample,1,start,(bad,0)))
    rejects('horizon domain exact',lambda bad=bad:Certificate(sample,bad,start,(0,0)))
for bad in (True,0.0,-1,Fraction(0,1)):
    rejects('atom threshold exact',lambda bad=bad:make(('eq',0,bad)))
rejects('opaque callable rejected',lambda:make(lambda a,b: True))
for bad in (('wat',),('not',True,False),('eq',2,0),('eq',True,0)):
    rejects('malformed AST rejected',lambda bad=bad:make(bad))
f=Certificate(sample,1,start,(0,0))
for bad in (True,0.0,-1,Fraction(0,1)):
    w=list(f.witness());w[0]=bad
    rejects('witness natural domain exact',lambda w=w:f.evaluate(w))
rejects('witness dimension exact',lambda:f.evaluate([]))
freal=Certificate(sample,1,start,(0,0),nonnegative_real=True)
for bad in (True,0.0,-1):
    w=list(freal.witness());w[0]=bad
    rejects('real evaluator exact domain',lambda w=w:freal.evaluate(w))

# Deep immutable snapshots, schema strictness, flag defenses, no float coercion.
raw=json.loads(Path('sample-source.json').read_text())
m,s=load_machine(raw)
raw['controls'][0]='MUTATED';raw['branches'][0]['guard']['op']='false'
check('source snapshot',m.controls[0]=='START' and m.transition('START',(0,0)) is not None)
guard=['and',['eq',0,0],['eq',1,0]]
b=Branch('b','A','H',0,0,guard);guard[1][2]=9
check('AST snapshot',guard_value(b.guard,(0,0)))
controls=['A','H'];branches=[b];m=Machine(controls,branches,'H',0);controls[0]='MUTATED';branches.clear()
check('container snapshot',m.controls==('A','H') and len(m.branches)==1)
for fn in (lambda:setattr(m,'J',3),lambda:setattr(b,'delta',1),lambda:setattr(f,'H',4),
           lambda:f.machine.control_codes.__setitem__('START',99),lambda:f._add('late',[(1,())]),lambda:f._var('late')):
    rejects('immutable snapshots',fn)
for field,value in [('class_cut',True),('start',[]),('schema','bad')]:
    raw=json.loads(Path('sample-source.json').read_text());raw[field]=value
    rejects('strict JSON schema',lambda raw=raw:load_machine(raw))
raw=json.loads(Path('sample-source.json').read_text());raw['extra']=0
rejects('extra top-level key rejected',lambda:load_machine(raw))
raw=json.loads(Path('sample-source.json').read_text());raw['branches'][0]['guard']['extra']=0
rejects('extra AST key rejected',lambda:load_machine(raw))
rejects('non-Boolean clock flag',lambda:Certificate(sample,1,start,(0,0),clock=1))
rejects('non-Boolean real flag',lambda:Certificate(sample,1,start,(0,0),nonnegative_real=1))

# Constructors must not mutate existing frozen objects on a second __init__.
for fn in (lambda:b.__init__('evil','A','H',0,1,True),
           lambda:m.__init__(['A','H'],[],'H',0),
           lambda:m.cells[0].__init__(0,(1,1)),
           lambda:f.__init__(sample,1,start,(1,0))):
    rejects('constructor reinitialization rejected',fn)
check('reinitialization leaves source unchanged',m.transition('A',(0,0))==(0,'H',(0,0)))
for field,value in [('controls',('START','HALT'))]:
    raw=json.loads(Path('sample-source.json').read_text());raw[field]=value
    rejects('JSON arrays exact list',lambda raw=raw:load_machine(raw))
class StringSubclass(str):
    pass
raw=json.loads(Path('sample-source.json').read_text());raw['schema']=StringSubclass(raw['schema'])
rejects('JSON schema exact string',lambda:load_machine(raw))
raw=json.loads(Path('sample-source.json').read_text());raw['branches'][0]['guard']={'op':'false'}
rejects('shared schema false op rejected',lambda:load_machine(raw))
raw=json.loads(Path('sample-source.json').read_text());raw['branches'][0]['guard']={'op':'or','args':[]}
false_machine,_=load_machine(raw)
check('shared schema false via empty or',not false_machine.cells)
cyclic=['not',None];cyclic[1]=cyclic
rejects('cyclic kernel AST rejected',lambda:make(cyclic))
cyclic_json={'op':'not'};cyclic_json['arg']=cyclic_json
raw=json.loads(Path('sample-source.json').read_text());raw['branches'][0]['guard']=cyclic_json
rejects('cyclic JSON AST rejected',lambda:load_machine(raw))
deep={'op':'true'}
for _ in range(2500):
    deep={'op':'not','arg':deep}
raw=json.loads(Path('sample-source.json').read_text());raw['branches'][0]['guard']=deep
deep_machine,_=load_machine(raw)
check('deep finite AST accepts without recursion',deep_machine.transition('START',(0,0))==(0,'HALT',(1,0)))

empty_name=Machine(['','H'],[Branch('','','H',0,0,True)],'H',0)
check_certificate(Certificate(empty_name,1,'',(0,0)),True)

# Full clean-target wrapper certificate, with original H1 becoming source H4.
clean,clean_start=load_machine(json.loads(Path('clean-target-sample-source.json').read_text()))
for real in (False,True):
    cf=Certificate(clean,4,clean_start,(0,0),clock=True,nonnegative_real=real)
    check_certificate(cf,True)
    check('cleanup clock2834',cf.witness()[cf.theta]==2834)
    check('cleanup restores both counters',tuple(cf.witness()[i] for i in cf.counters[-1])==(0,0))
    check('cleanup normalization ledger',cf.ledger()['normalized_branches']==33 and cf.ledger()['tail_occurrences']==23 and cf.ledger()['normalized_nonzero_branches']==15)
    check('cleanup exact ledger',len(cf.names)==233 and len(cf.residuals)==282+4*int(real))
    cf.export('clean-target-real-certificate.json' if real else 'clean-target-certificate.json')
    Path('clean-target-real-witness.json' if real else 'clean-target-witness.json').write_text(json.dumps(cf.witness())+'\n')
for H in (0,1,2,3,5):
    check_certificate(Certificate(clean,H,clean_start,(0,0),clock=True),False)

receipt=dict(status='PASS',test_assertions=sum(checks.values()),checks=checks,complete_fiber_tests=fibers,
             sample=Certificate(sample,1,start,(0,0),clock=True).ledger(),
             caveat='Exact implementation checks; all-horizon uniqueness is proved in PROOF.md. CA simulation is separately audited.')
Path('test-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
