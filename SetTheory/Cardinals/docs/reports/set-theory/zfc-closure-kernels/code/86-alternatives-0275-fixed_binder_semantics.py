"""Finite diagnostics for fixed-label CP/GIC specialization.
These independently compare exact named formula trees with direct semantics.
They are not a proof of all-code soundness or a compiler simulation.
"""
from __future__ import annotations
from itertools import product
import json
from pathlib import Path

I=lambda a,b:('imp',a,b)
R=lambda a,b:('rel',a,b)
A=lambda a,b:('all',a,b)
F=R(0,0)
N=lambda a:I(a,F)
C=lambda a,b:N(I(a,N(b)))
E=lambda a,b:N(A(a,N(b)))

# Copied as formulas, rather than invoking the upstream symbolic evaluator.
def container(a,b,c):
    p=E(c,C(A(b,I(A(c,I(R(c,b),R(c,a))),R(b,c))),R(c,b)))
    tr=A(c,I(R(c,a),R(c,b)))
    return E(b,C(A(a,I(R(a,b),C(p,tr))),R(c,b)))

def gic(a,b,k,phi):
    w=E(b,C(phi,R(b,k)))
    return E(k,C(A(a,I(R(a,b),A(b,I(phi,w)))),A(b,I(R(b,k),E(a,phi)))))

def sat(t,env,rel,phi):
    if t=='phi': return phi[env[0]][env[1]]
    if t=='truth': return True
    op,x,y=t
    if op=='rel': return rel[env[x]][env[y]]
    if op=='imp': return not sat(x,env,rel,phi) or sat(y,env,rel,phi)
    if op=='all':
        return all(sat(y,dict(env,**{} )|{x:v},rel,phi) for v in range(len(rel)))
    raise ValueError(op)

def direct_gic(rel,phi,domain):
    n=len(rel)
    return any(all(not rel[y][b] or any(phi[x][y] for x in range(n)) for y in range(n))
      and all(not rel[x][domain] or not any(phi[x]) or any(phi[x][y] and rel[y][b] for y in range(n)) for x in range(n)) for b in range(n))

def direct_container(rel,seed):
    n=len(rel)
    sub=lambda a,b:all(not rel[x][a] or rel[x][b] for x in range(n))
    return any(rel[seed][v] and all(not rel[x][v] or (sub(x,v) and any(rel[b][v] and all(not sub(z,x) or rel[z][b] for z in range(n)) for b in range(n))) for x in range(n)) for v in range(n))

def relation(n,mask):
    edges=[(x,y) for x in range(n) for y in range(n) if x!=y]
    a=[[False]*n for _ in range(n)]
    for bit,(x,y) in enumerate(edges):a[x][y]=bool(mask>>bit&1)
    return a

def run():
    counts={'fixed_C_exact_cases':0,'fixed_G_fresh_exact_cases':0,'zero_alias_offset1_empty_cases':0}
    for n in (1,2,3):
        for mask in range(1<<(n*(n-1))):
            rel=relation(n,mask)
            for seed in range(n):
                env={i:0 for i in range(5)};env[2]=seed
                assert sat(container(0,1,2),env,rel,None)==direct_container(rel,seed)
                counts['fixed_C_exact_cases']+=1
            empty=any(all(not rel[x][v] for x in range(n)) for v in range(n))
            env={i:0 for i in range(5)}
            assert sat(gic(0,1,1,'truth'),env,rel,None)==empty
            counts['zero_alias_offset1_empty_cases']+=1
            for p in range(1<<(n*n)):
                phi=[[bool(p>>(x*n+y)&1) for y in range(n)] for x in range(n)]
                for domain in range(n):
                    env={i:0 for i in range(5)};env[1]=domain
                    assert sat(gic(0,1,4,'phi'),env,rel,phi)==direct_gic(rel,phi,domain)
                    counts['fixed_G_fresh_exact_cases']+=1
    counts['all_passed']=True
    counts['proof_status']='Finite tests only; all-domain mathematical proofs are in fixed_binder_routes.md.'
    return counts
if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run without -O: assertions are part of these diagnostics.')
    r=run();path=Path(__file__).with_name('fixed_binder_semantics_results.json');path.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
