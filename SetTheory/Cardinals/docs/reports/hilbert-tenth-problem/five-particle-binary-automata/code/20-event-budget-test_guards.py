"""Additional general scheduler checks: guard rejection, p=0, b=0, Delta=2."""
import json,random
from pathlib import Path
import scheduler_reference as s
H=Path(__file__).resolve().parent

def src(branches,J=0):
    return dict(schema='reversible-two-counter-v1',controls=['q','halt'],start='q',halt='halt',class_cut=J,branches=branches)
def branch(name,delta,guard):return dict(name=name,source='q',target='halt',side=1,delta=delta,guard=guard)
def check(v,d):
    if not v:raise RuntimeError(d)
def main():
    sources=[src([]),src([branch('nop',0,dict(op='true'))]),
      src([branch('zero',0,dict(op='eq',counter=1,value=0)),branch('pos',1,dict(op='gt',counter=1,value=0))],1)]
    rng=random.Random(3102026);count=0;multi_context=0
    ledgers=[]
    for data in sources:
        a=s.lazy.compile_lazy_source(data);e=s.lazy.ref.compile_source(data)
        cases=[frozenset(),frozenset({0}),frozenset({-10**200,10**200})]
        for q in a.controls:
            for c0 in range(3):
                for c1 in range(3):
                    for sign in ('+','-'):cases.append(a.encode(q,c0,c1,sign))
        for _ in range(50):
            g=a.gate_at(rng.randrange(a.factors));shape=rng.choice(g.shapes);x=frozenset(shape)
            cases.extend([x,x|{-a.Z,a.Z},x|{-a.Z,a.Z,a.Z+1},x|{a.Z+1},x|{v+3*a.Z for v in x}])
            multi_context+=1
        for x in cases:
            check({i for on,i in s.slots(a,x) if on}==set(a.candidate_indices(x)),('candidates',a.ledger(),x))
            y,st=a.step(x,trace=True);check(y==e.step(x),'eager')
            ok,z,rounds=s.run(a,x,1,st['changed_factors']+1)
            check(ok and z==y,('scheduler',a.ledger(),x));count+=1
        ledgers.append(a.ledger())
    result=dict(status='passed',optimized=not __debug__,cases=count,sources=ledgers,generated_context_families=multi_context)
    name='guard-optimized-receipt.json' if not __debug__ else 'guard-receipt.json'
    (H/name).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
