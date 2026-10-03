"""Standard-library bounded regression. All checks survive python -O."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import time
from parallel_particles import ParallelCompiler

ROOT = Path(__file__).resolve().parent
COUNTS = {}

def check(value, detail):
    if not value:
        raise RuntimeError(detail)


def source(side=1, delta=1, guard=None, J=0):
    if guard is None:
        guard = {'op':'true'}
    return dict(schema='reversible-two-counter-v1', controls=['q','h'],start='q',halt='h',class_cut=J,
                branches=[dict(name='e',source='q',target='h',side=side,delta=delta,guard=guard)])


def fusion(side):
    idx = (side+1)//2
    zero = dict(op='eq',counter=idx,value=0)
    pos = dict(op='gt',counter=idx,value=0)
    def row(n,s,t,d,g):
        return dict(name=n,source=s,target=t,side=side,delta=d,guard=g)
    return dict(schema='reversible-two-counter-v1',controls=['q','z','p','h'],start='q',halt='h',class_cut=1,
                branches=[row('zero','q','z',0,zero),row('pos','q','p',0,pos),
                          row('incz','z','h',1,zero),row('incp','p','h',1,pos)])


def flip(c, x):
    pairs=[(a,b) for a in x for b in x if 0 < b-a <= c.D]
    check(len(pairs)==1, ('ambiguous head',x))
    a,b=pairs[0]
    mode,sign=next(k for k,v in c.gap.items() if v==b-a)
    return frozenset((x-{b}) | {a+c.gap[(mode,'-' if sign=='+' else '+')]})


def micro_path(c,c0,c1):
    """Independent source-edge subdivision, without CA/template execution."""
    q=c.start; cs=[c0,c1]; states=[c.encode(q,*cs)]; times=[]
    for _ in range(20):
        choices=[e for e in c.branches if e.source==q and e.guard(*cs)]
        check(len(choices)<=1,'source nondeterminism')
        if not choices:
            return states,times
        e=choices[0]; v=e.side; idx=(v+1)//2; began=len(states)-1
        if e.delta==0:
            q=e.target;states.append(c.encode(q,*cs));times.append(1);continue
        old=cs[idx]
        markers=[-c.Z-cs[0],0,c.Z+cs[1]]
        def state(kind,anchor):
            return frozenset(markers+[anchor,anchor+c.gap[((kind,e.name),'+')]])
        anchor=v*c.S; states.append(state('O',anchor))
        target=markers[0 if v==-1 else 2]-v*c.S
        while anchor!=target:
            anchor+=v;states.append(state('O',anchor))
        cs[idx]+=e.delta;markers=[-c.Z-cs[0],0,c.Z+cs[1]]
        anchor=markers[0 if v==-1 else 2]-v*c.S;states.append(state('I',anchor))
        target=v*c.S
        while anchor!=target:
            anchor-=v;states.append(state('I',anchor))
        q=e.target;states.append(c.encode(q,*cs))
        elapsed=len(states)-1-began
        check(elapsed==3+2*(c.Z+old)+e.delta-4*c.S, 'microedge clock')
        times.append(elapsed)
    raise RuntimeError('Unexpected long source computation')


def valid_tests():
    checked=full_steps=old_comparisons=0; ledgers=[]
    cases=[]
    for side in (-1,1):
        idx=(side+1)//2
        cases += [(source(side,1),0,0,True),
                  (source(side,-1,dict(op='gt',counter=idx,value=0)),2,2,False),
                  (source(side,-1,dict(op='gt',counter=idx,value=0)),0,0,True),
                  (fusion(side),0,0,False),(fusion(side),2,2,False)]
    cases += [(source(1,0),0,4,True)]
    clean=json.loads((ROOT/'clean-target-sample-source.json').read_text())
    cases += [(clean,0,0,True)]
    for data,c0,c1,complete in cases:
        p=ParallelCompiler(data); c=p.old; path,times=micro_path(c,c0,c1)
        cycle=path+[flip(c,x) for x in reversed(path)]
        indices=set(range(len(cycle))) if complete else {0,len(path)-1,len(path),len(cycle)-1}
        if not complete:
            indices.update(range(0,len(cycle),79))
            for i,x in enumerate(cycle):
                pair=next((a,b) for a in x for b in x if 0<b-a<=c.D)
                anchor=pair[0]; markers=x-set(pair)
                if any(abs(anchor-m) in {c.S,c.S+1,c.L-1,c.L,c.L+1,c.L+2} for m in markers):
                    indices.add(i)
        for i in sorted(indices):
            x=cycle[i]; want=cycle[(i+1)%len(cycle)]
            got=p.step(x)
            check(got==want,('trajectory',data,c0,c1,i,sorted(got),sorted(want)))
            check(p.step(got,inverse=True)==x,('inverse',i))
            # BOTH signed copies of every tested node retain at most one edge
            # candidate and exactly one phase candidate, with no filter rejection.
            for block,allow_absent in [(p.E,True),(p.P,False)]:
                raw=block.candidates(x);active=block.eligible(x,raw)
                check(len(raw)<=1 if allow_absent else len(raw)==1,('matching',i,raw))
                check(set(raw)==set(active),('valid filter rejection',i,raw,active))
            if i in {0,1,len(path)-2,len(path)-1,len(path),len(cycle)-1} or i%317==0:
                check(c.step(x)==got,('old compiler mismatch',i));old_comparisons+=1
                p.E.apply(x,True);p.P.apply(x,True)
            checked+=1
        if complete:full_steps+=len(cycle)
        ledgers.append(dict(ledger=p.ledger(),counters=[c0,c1],source_times=times,
                            cycle_length=len(cycle),tested_states=len(indices),complete_cycle=complete))
    COUNTS.update(valid_tested_states=checked,complete_cycle_states=full_steps,
                  eager_old_step_comparisons=old_comparisons,source_cases=ledgers)


def malformed_tests():
    p=ParallelCompiler(source());c=p.old
    x=frozenset([-118,-112,0,18,23]);cascade={}
    for name in ['E','P']:
        b=getattr(p,name)
        raw=b.candidates(x);active=b.eligible(x,raw)
        check(len(raw)==1 and not active,('cascade not prospectively rejected',name))
        key,label=next(iter(raw.items())); naive=b.swap(x,key,label)
        new_keys=b.candidates(naive)
        check(set(new_keys)!=set(raw),('missing new key',name))
        check(b.apply(x,True)==x,('cascade not frozen',name))
        gates=getattr(c,name)
        def ordered(z):
            for g in gates:z=g.apply(z)
            return z
        check(ordered(ordered(x))!=x,('old block unexpectedly involutive',name))
        cascade[name]=dict(initial_candidates=[[cname(c,name,k[0]),k[1],v] for k,v in raw.items()],
                           after_single_swap=sorted(naive),
                           new_candidates=[[cname(c,name,k[0]),k[1],v] for k,v in new_keys.items()],
                           old_twice=sorted(ordered(ordered(x))))
    check(p.step(x)==x and c.step(x)!=x,'new and old rules should differ')
    universes=[[-119,-118,-114,-113,-112,0,18,19,23,24,25],
               [-380,-19,-18,-17,-13,-12,-10,-9,0,1,380]]
    exhaustive=0
    for universe in universes:
        for mask in range(1<<len(universe)):
            z=frozenset(t for i,t in enumerate(universe) if mask>>i&1)
            y=p.step(z,verify=True)
            check(p.step(y,inverse=True)==z,('malformed inverse',z))
            exhaustive+=1
    rng=random.Random(20261003);random_cases=0;translated=0;local_checks=0
    # Construct widely separated blocks so genuine simultaneous updates occur.
    base=c.encode('q',2,4)
    far=3*p.E.H
    z=base|{t+far for t in base}
    check(len(p.E.eligible(z))==2,'missing simultaneous edge swaps')
    p.E.apply(z,True)
    simultaneous=dict(input=sorted(z),edge_selected=len(p.E.eligible(z)),phase_selected=len(p.P.eligible(z)))
    for trial in range(100):
        z=set(base if trial%3 else x)
        if trial%4==0:z.update(t+far for t in base)
        for _ in range(rng.randrange(1,9)):
            t=rng.randrange(-2*c.Z,2*c.Z)
            if t in z:z.remove(t)
            else:z.add(t)
        z=frozenset(z);y=p.step(z,True,True)
        check(p.step(y)==z,('random inverse',trial));random_cases+=1
        shift=rng.randrange(-1000,1001)
        check(p.step({t+shift for t in z})=={t+shift for t in p.step(z)},'translation');translated+=1
        for b in (p.E,p.P):
            by=b.apply(z)
            for i in sorted(z | by)[:12]:
                check(b.local_output(z,i)==int(i in by),('local radius mismatch',trial,i))
                local_checks+=1
    COUNTS.update(malformed_exhaustive=exhaustive,malformed_random=random_cases,
                  translations=translated,local_radius_checks=local_checks,
                  cascade=cascade,simultaneous=simultaneous)


def cname(c,name,j):
    return getattr(c,name)[j].name


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    began=time.perf_counter()
    check(hashlib.sha256((ROOT/'frozen_reversible_binary.py').read_bytes()).hexdigest()==
          'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f','frozen compiler SHA')
    valid_tests();print('valid state tests passed',flush=True)
    malformed_tests();print('malformed tests passed',flush=True)
    out=dict(status='passed',counts=COUNTS,elapsed_seconds=time.perf_counter()-began)
    print(json.dumps(out,indent=2))
    import sys
    dest=args.output_dir/('test-receipt-optimized.json' if sys.flags.optimize else 'test-receipt.json')
    dest.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
