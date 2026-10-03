"""Independent periodic full-shift regressions for the general lemma.

No materialized source compiler is used. Small tori exhaust all binary words,
including dense backgrounds and multiple simultaneously selected moves.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
import time
from parallel_particles import ParallelBlock, Pattern

ROOT=Path(__file__).resolve().parent

def check(x,message):
    if not x:raise RuntimeError(message)

class BitGuard:
    def __init__(self,offset,value):self.offset,self.value=offset,value
    def allows(self,x,u):return int(u+self.offset in x)==self.value


def run_case(n, templates, b, r):
    H=2*(b+r)
    def dist(a,z):return min((a-z)%n,(z-a)%n)
    def candidates(bits):
        found={}
        for j,(p,q,iso,guard) in enumerate(templates):
            for u in range(n):
                actual=frozenset(d for d in range(-iso,iso+1) if bits[(u+d)%n])
                if guard and bits[(u+guard[0])%n]!=guard[1]:continue
                if actual==p:found[j,u]=0
                elif actual==q:found[j,u]=1
        return found
    def swapped(bits,k,label):
        j,u=k;p,q,_,_=templates[j]
        old,new=(p,q) if label==0 else (q,p)
        y=list(bits)
        for d in old:y[(u+d)%n]=0
        for d in new:y[(u+d)%n]=1
        return tuple(y)
    def selected(bits,raw=None,prospective=True):
        raw=candidates(bits) if raw is None else raw;out={}
        for k,v in raw.items():
            if any(l!=k and dist(l[1],k[1])<=H for l in raw):continue
            if prospective and set(candidates(swapped(bits,k,v)))!=set(raw):continue
            out[k]=v
        return out
    def apply(bits,prospective=True):
        raw=candidates(bits);active=selected(bits,raw,prospective)
        y=bits
        for k,v in active.items():y=swapped(y,k,v)
        return y,raw,active
    patterns=[Pattern(str(j),p,q,iso,None if guard is None else BitGuard(*guard))
              for j,(p,q,iso,guard) in enumerate(templates)]
    local=ParallelBlock(patterns,b,r)
    words=changed=multi=local_checks=0;mutation=None
    for mask in range(1<<n):
        bits=tuple((mask>>i)&1 for i in range(n))
        out,raw,active=apply(bits)
        back,raw2,active2=apply(out)
        check(back==bits,('noninvolution',mask,n,templates))
        check(sum(out)==sum(bits),('mass',mask))
        check(set(raw2)==set(raw),('candidate changed',mask))
        check(set(active2)==set(active),('selection changed',mask))
        changed+=out!=bits;multi+=len(active)>1;words+=1
        # Exhaustive coordinate-0 local rule agreement implies agreement at every
        # translated word, since all cyclic words are included in the suite.
        window=frozenset(z for z in range(-local.radius,local.radius+1) if bits[z%n])
        check(local.local_output(window)==out[0],('local oracle',mask,n))
        local_checks+=1
        if mutation is None:
            naive,_,_=apply(bits,False)
            naive_back,_,_=apply(naive,False)
            if naive_back!=bits:
                mutation=dict(input=[i for i,v in enumerate(bits) if v],
                              first=[i for i,v in enumerate(naive) if v],
                              second=[i for i,v in enumerate(naive_back) if v])
    return dict(period=n,b=b,r=r,exclusion=H,radius=local.radius,types=len(templates),
                exhaustive_words=words,changed_words=changed,multiple_move_words=multi,
                local_checks=local_checks,missing_prospectivity_counterexample=mutation)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    started=time.perf_counter()
    p,q=frozenset([-1,0]),frozenset([-1,1])
    runs=[run_case(12,[(p,q,1,None)],1,1),
          run_case(14,[(p,q,1,(2,0))],1,2),
          run_case(12,[(p,q,1,None),(frozenset([0,1]),q,1,None)],1,1)]
    check(runs[0]['multiple_move_words']>0,'no simultaneous test evidence')
    check(runs[0]['missing_prospectivity_counterexample'] is not None,'mutation not killed')
    receipt=dict(status='passed',runs=runs,elapsed_seconds=time.perf_counter()-started)
    print(json.dumps(receipt,indent=2))
    (args.output_dir/('periodic-receipt-optimized.json' if sys.flags.optimize else 'periodic-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
