"""Reproduce exact regressions and write data/checks.json; no dependencies."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt, lcm
from pathlib import Path
import json
import random
from signal_certificates import Machine, InvalidSkeleton, compile_skeleton, simulate, dot, UnionCertificate

ROOT=Path(__file__).resolve().parents[1]
summary={"status":"PASS", "arithmetic":"Python Fraction and integer arithmetic",
         "scope":"finite regression tests; not formal verification", "checks":{}}
count=0

def check(condition, message):
    global count
    count+=1
    if not condition:
        raise AssertionError(message)

# A first-collision tournament with an explicit triple-collision rule.
tournament=Machine({'A':2,'B':0,'C':-1,'H':0,'R':0}, {
    frozenset(('A','B')):('H',),
    frozenset(('B','C')):('R',),
    frozenset(('A','B','C')):('R',)})
initial=('A','B','C')
sleft=(((0,1),),); sright=(((1,2),),); striple=(((0,1,2),),)
cleft=compile_skeleton(tournament,initial,sleft)
cright=compile_skeleton(tournament,initial,sright)
ctriple=compile_skeleton(tournament,initial,striple)
for u,v in product(range(1,41),repeat=2):
    run=simulate(tournament,initial,(u,v),1)
    for c,sk,truth in ((cleft,sleft,u<2*v),(cright,sright,u>2*v),
                        (ctriple,striple,u==2*v)):
        check(c.accepts((u,v))==truth,"tournament chamber")
        check((run.skeleton==sk)==truth,"tournament simulator")
        if truth:
            w=c.witnesses((u,v))
            check(c.evaluate((u,v),w)==0,"constructed zero")
            for j in range(len(w)):
                bad=list(w); bad[j]+=1
                check(c.evaluate((u,v),bad)>0,"one-coordinate witness mutation")
check(not cleft.accepts((3,1)),"earlier collision must not be omitted")
check(not cleft.accepts((2,1)),"simultaneous third input must not be omitted")
summary['checks']['tournament_seeds']=1600

# Exact count, rational generating-function recurrence, and inverse threshold.
counts=[]
for H in range(81):
    actual=sum(u<2*v for u,v in product(range(1,H+1),repeat=2))
    formula=(3*H*H+1)//4
    check(actual==formula,"quadratic quasi-polynomial count")
    counts.append(actual)
for y in range(1,2001):
    # ceil(sqrt((4*y-1)/3)), using integer arithmetic only.
    target=4*y-1
    n=isqrt(target//3)
    if 3*n*n<target: n+=1
    check((3*n*n+1)//4>=y,"inverse upper")
    check(n==0 or (3*(n-1)*(n-1)+1)//4<y,"inverse minimality")
# Denominator (1-z)^3(1+z)=1-2z+0z^2+2z^3-z^4.
for n in range(5,len(counts)):
    check(counts[n]-2*counts[n-1]+2*counts[n-3]-counts[n-4]==0,
          "generating-function recurrence")
summary['checks']['count_boxes']=81
summary['checks']['inverse_thresholds']=2000

# Multiple independent collision sites at exactly the same time.
transparent=Machine({'P':1,'N':-1},{})
simultaneous=(((0,1),(2,3)),)
cs=compile_skeleton(transparent,('P','N','P','N'),simultaneous)
check(cs.accepts((2,5,2)),"two simultaneous sites")
check(not cs.accepts((2,5,3)),"false simultaneity")
cmissing=compile_skeleton(transparent,('P','N','P','N'),(((0,1),),))
check(not cmissing.accepts((2,5,2)),"omitted independent simultaneous site")
check(simulate(transparent,('P','N','P','N'),(2,5,2),1).skeleton==simultaneous,
      "reference simultaneous run")

# A four-speed Zeno clock; all finite prefixes are ordinary legal executions.
clock=Machine({'L':0,'P':2,'R':-1,'N':-2}, {
    frozenset(('P','R')):('N','R'),
    frozenset(('L','N')):('L','P')})
clock_run=simulate(clock,('L','P','R'),(1,2),24)
cc=compile_skeleton(clock,('L','P','R'),clock_run.skeleton)
for j,t in enumerate(clock_run.times,1):
    if j%2:
        k=(j-1)//2
        expected=F(3)-F(7,3**(k+1))
    else:
        k=j//2
        expected=F(3)-F(7,2*3**k)
    check(t==expected,"Zeno exact times")
    check(dot(cc.times[j-1],(1,2))==t,"symbolic time reconstruction")
    check(12**cc.depths[j-1] % t.denominator == 0,"causal denominator bound")
for gaps in product(range(1,6),repeat=2):
    check(cc.accepts(gaps),"whole positive quadrant clock chamber")
    check(simulate(clock,('L','P','R'),gaps,24).skeleton==clock_run.skeleton,
          "clock skeleton independent of positive gaps")
summary['checks']['clock_batches']=24
summary['checks']['clock_parameter_seeds']=25
summary['clock_times']=[str(t) for t in clock_run.times[:12]]

# A branching/annihilating example and independent random cross-validation.
rng=random.Random(20261002)
comparisons=0; distinct_skeletons=0; machines_tested=0
for trial in range(6):
    names=('A','B','C','D')
    speeds=dict(zip(names,(-2,-1,1,2)))
    rules={}
    for size in range(2,5):
        for inc in combinations(names,size):
            # Includes creation, annihilation, and transparent-looking rules.
            out=tuple(x for x in names if rng.randrange(2))
            rules[frozenset(inc)]=out
    machine=Machine(speeds,rules)
    labels=tuple(rng.choice(names) for _ in range(4))
    seeds=list(product(range(1,5),repeat=3))
    runs={g:simulate(machine,labels,g,4) for g in seeds}
    skeletons=set()
    for run in runs.values():
        for k in range(1,len(run.skeleton)+1):
            skeletons.add(run.skeleton[:k])
    for sk in sorted(skeletons):
        cert=compile_skeleton(machine,labels,sk)
        for g,run in runs.items():
            expected=(len(run.skeleton)>=len(sk) and run.skeleton[:len(sk)]==sk)
            check(cert.accepts(g)==expected,"independent random chamber comparison")
            comparisons+=1
            if expected:
                check(cert.evaluate(g,cert.witnesses(g))==0,"random zero")
                for form,dep in zip(cert.event_times,cert.depths):
                    value=dot(form,g)
                    check(12**dep % value.denominator==0,"random denominator bound")
        distinct_skeletons+=1
    machines_tested+=1
summary['checks']['random_machines']=machines_tested
summary['checks']['random_distinct_skeletons']=distinct_skeletons
summary['checks']['independent_parameter_skeleton_comparisons']=comparisons

# Negative validation cases are part of the input contract.
invalids=[(((0,2),),), (((1,2),(0,1)),), (((0,0),),), (((0,5),),), ((),)]
for sk in invalids:
    try:
        compile_skeleton(tournament,initial,sk)
    except InvalidSkeleton:
        check(True,"invalid skeleton correctly rejected")
    else:
        raise AssertionError("invalid skeleton accepted")
source={'A':1,'B':-1}
immutable=Machine(source,{})
source['A']=999
check(immutable.speeds['A']==1,"constructor must copy caller dictionaries")
try:
    immutable.speeds['A']=123
except TypeError:
    check(True,"speed table immutable")
else:
    raise AssertionError("mutable speed table")

# A disjoint first-hit union: change the triple rule to emit H as well.
# The first-batch chambers do not change, since H and R have the same speed.
union = UnionCertificate((cleft, ctriple))
union_seeds = 0
for u,v in product(range(1,41), repeat=2):
    if u <= 2*v:
        selectors,slacks=union.witnesses((u,v))
        check(union.evaluate((u,v),selectors,slacks)==0,"quartic union zero")
        off=0
        for b,c in zip(selectors,union.certificates):
            for z in slacks[off:off+len(c.strict)]:
                check(b==1 or z==0,"inactive slacks forced zero")
            off+=len(c.strict)
        wrong=list(selectors); wrong[0]+=1
        check(union.evaluate((u,v),wrong,slacks)>0,"invalid selector rejected")
    else:
        try:
            union.witnesses((u,v))
        except ValueError:
            check(True,"nonmember union seed")
        else:
            raise AssertionError("union accepted a nonmember")
    union_seeds+=1
summary['checks']['quartic_union_seeds']=union_seeds
ROOT.joinpath('data','first_hit_quartic_union.json').write_text(
    json.dumps(union.to_dict(),indent=2)+'\n')

# Export complete integer polynomial certificates as coefficient matrices.
ROOT.joinpath('data').mkdir(exist_ok=True)
exports={'tournament_left':cleft,'tournament_right':cright,
         'tournament_triple':ctriple,'simultaneous_two_sites':cs,
         'zeno_clock_24_batches':cc}
for name,cert in exports.items():
    ROOT.joinpath('data',name+'.json').write_text(json.dumps(cert.to_dict(),indent=2)+'\n')
summary['checks']['assertions']=count
summary['counts_first_21']=counts[:21]
summary['certificate_ledger']={name:{'equalities':len(c.equalities),'strict':len(c.strict),
    'intervals':c.intervals,'raw_rows':c.raw_rows,'row_bound':c.row_bound,
    'events':c.event_count,'batches':c.batch_count} for name,c in exports.items()}
ROOT.joinpath('data','checks.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
