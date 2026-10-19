#!/usr/bin/env python3
"""Local move-to-front transducer, not a complete ZFC consistency machine.

Default input is the pinned original-label Prefix246 table supplied alongside
this script. The verifier checks finite row identities underlying the stated
induction proofs and independent literal regression examples. The induction
arguments themselves are written in mtf-local.tex.
"""
from pathlib import Path
from hashlib import sha256
import argparse, itertools, json

HERE = Path(__file__).resolve().parent
PIN = '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
PATCH = {(75,0):(1,1,131), (112,1):(1,1,112), (131,0):(1,-1,48)}

def read(path):
    raw=path.read_bytes(); assert sha256(raw).hexdigest()==PIN
    t={}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,n=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    assert len(t)==492
    return t

def encode(t):
    return '#! start 95\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n'
        for (q,b),(w,d,n) in sorted(t.items()))

def step(t,q,h,ones):
    b=int(h in ones);w,d,n=t[q,b]
    if w:ones.add(h)
    else:ones.discard(h)
    return n,h+d,[q,h,b,w,d,n]

def run(t,q,h,ones,ticks):
    ones=set(ones);trace=[]
    for _ in range(ticks):q,h,row=step(t,q,h,ones);trace.append(row)
    return q,h,ones,trace

def blocks(vs):
    out=[]
    for v in vs:out += [0]+[1]*(v+1)
    return out

def mark(vs,r):
    out=blocks(vs);out[sum(v+2 for v in vs[:r])+1]=0
    return out

def ones_of(word,offset=0):return {offset+i for i,b in enumerate(word) if b}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,default=HERE/'reference246_old.tm')
    args=ap.parse_args();base=read(args.baseline);t={k:v for k,v in base.items() if k[0]!=255};t.update(PATCH)
    assert len(t)==490 and {n for w,d,n in t.values()}-{q for q,b in t}=={254}
    # Three literal rows implement one adjacent 10 -> 01 swap, with the
    # moving zero available for another inductive step. No exterior is read.
    q,h,o,bubble=run(t,112,0,{0},3)
    assert (q,h,o)==(112,-1,{1})
    assert [r[:3] for r in bubble]==[[112,0,1],[112,1,0],[131,0,1]]
    # The fixed leading 10 of C(v) becomes 01 in two moves.
    q,h,o,leading=run(t,112,1,{0},2)
    assert (q,h,o)==(112,-1,{1})
    # The selected 00 and compulsory following 01 are restored in nine
    # literal moves, leaving state112 immediately to the left.
    q,h,o,boundary=run(t,95,0,{3},9)
    assert (q,h,o)==(112,-1,{1,3})
    # The two four-step blank-end closures have exactly identical endpoints.
    q,h,o,old_tail=run(base,75,0,{-2},4)
    q2,h2,o2,new_tail=run(t,75,0,{-2},4)
    assert (q,h,o)==(q2,h2,o2)==(48,-2,{-2,0,1})
    # Independent finite regression of the full local operations.
    count=0
    for n in range(4):
        for A in itertools.product(range(4),repeat=n):
            for S in ([0],[1],[2,0,3]):
                for x in range(4):
                    vs=list(A)+[x]+S;prefix={-9,-7,-5,-1};initial=prefix|ones_of(mark(vs,n))
                    q,h,o,_=run(t,95,0,initial,4*sum(A)+4*n+9 if x==0 else 2*sum(v+2 for v in A)+4)
                    if x==0:want=prefix|ones_of(blocks([0]+list(A)+S));goal=(112,-1,want)
                    else:want=prefix|{0}|ones_of(blocks(list(A)+[x-1]+S),1);goal=(48,0,want)
                    assert (q,h,o)==goal,(A,x,S,'decrement')
                    width=sum(v+2 for v in vs)
                    q,h,o,_=run(t,73,0,initial,2*width+7)
                    assert (q,h,o)==(48,-1,prefix|ones_of(blocks(list(A)+[x+1]+S+[1]))),(A,x,S,'increment')
                    count+=2
    # This fixed header continuation is why the local lemma does not supply
    # a complete branch-preserving interpreter.
    before={-1,1,3}
    qb,hb,ob,tb=run(base,112,-1,before,3)
    qu,hu,ou,tu=run(t,112,-1,before,5)
    assert (qb,hb,ob)==(48,-4,{-2,-1,1,3})
    assert (qu,hu,ou)==(48,-4,{-3,-2,0,1,3})
    assert ob!=ou
    text=encode(t);(HERE/'candidate-mtf245-local.tm').write_text(text,encoding='ascii')
    out=dict(status='PASS',scope='Local ordinary-induction premises plus finite regressions; not a complete consistency machine.',
        baseline_sha256=PIN,candidate_sha256=sha256(text.encode()).hexdigest(),states=245,rows=490,
        patch=[[q,b,*v] for (q,b),v in PATCH.items()],removed_state=255,local_regression_cases=count,
        universal_lemma='Zero: B(A)00B(S) -> B([0]++A++S); positive decrement and increment unchanged.',
        zero_steps='4*sum(A)+4*len(A)+9',bubble=bubble,leading=leading,zero_boundary=boundary,
        old_tail=old_tail,new_tail=new_tail,
        header_obstruction=dict(input_ones=sorted(before),baseline=dict(steps=3,state=qb,head=hb,ones=sorted(ob),trace=tb),
            mutant=dict(steps=5,state=qu,head=hu,ones=sorted(ou),trace=tu)),
        complete_conditional_runtime=False,proved_zfc_equivalence=False,new_proof_assistant_endpoint=False)
    (HERE/'mtf-verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('bubble','leading','zero_boundary','old_tail','new_tail','header_obstruction')},indent=2))

if __name__=='__main__':main()
