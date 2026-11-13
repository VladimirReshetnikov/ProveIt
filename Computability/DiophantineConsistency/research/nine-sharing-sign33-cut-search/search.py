#!/usr/bin/env python3
"""Bounded conditional signed-cut search; no Lean, no global optimality claim."""
import collections, hashlib, json, random, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent; D=P.parents[1]
source=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
raw=source.read_bytes(); assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw); rows=g['source'][:60]; terminal={'N0','N1','Nt','Na','scaled_Ns'}
names=[row[0] for row in rows if row[0] not in terminal and row[0] not in {'qm','q'}]
mx=lambda a,b:b if a is None else a if b is None else max(a,b)
mul=lambda a,b:None if a is None or b is None else a+b
rng=random.Random(20261106); cache={}
def run(cuts):
    key=tuple(sorted(cuts.items()))
    if key in cache: return cache[key]
    env={n:(1,None) for n in g['witnesses']};env.update({n:(0,None) for n in g['fixed_numerals']}); obligations=[]
    for name,op,left,right in rows:
        def get(x): return (0,None) if type(x) is int else env[x]
        ap,an=get(left);bp,bn=get(right)
        if op=='+': x,y=mx(ap,bp),mx(an,bn)
        elif op=='-': x,y=mx(ap,bn),mx(an,bp)
        elif op=='*': x,y=mx(mul(ap,bp),mul(an,bn)),mx(mul(ap,bn),mul(an,bp))
        else: raise ValueError(op)
        if mx(x,y)>2:
            opts=sorted({j for j in (left,right) if isinstance(j,str) and j not in cuts and j in names and mx(*env[j])>1})
            cache[key]=(False,opts,[]);return cache[key]
        if name in cuts:
            sign=cuts[name]
            # Every single-coordinate signed cut is conditional on the chosen
            # source gate sign; a structurally zero component discharges it.
            if (sign==1 and y is not None) or (sign==-1 and x is not None):obligations.append([name,sign])
            env[name]=(1,None) if sign==1 else (None,1)
        else:env[name]=(x,y)
    cache[key]=(True,[],obligations);return cache[key]
def repair(cuts):
    c=dict(cuts)
    for _ in range(len(names)+1):
        ok,opts,_=run(c)
        if ok:return c
        if not opts:return None
        n=rng.choice(opts);c[n]=-1 if n=='V2minusY2' else 1
    return None
def prune(cuts):
    c=dict(cuts);order=list(c);rng.shuffle(order)
    for n in order:
        if n=='q2':continue
        trial=dict(c);del trial[n]
        if run(trial)[0]:c=trial
    return c
baseline={'Dc2','Delta','E','V','V2minusY2','X','Y','c2','cTminusR','ell','f2','gap','kY','main_root','normalized_S','normalized_S2','q2','q3','tau'}
baseline={n:(-1 if n=='V2minusY2' else 1) for n in baseline};assert run(baseline)[0]
best=baseline;pool=[baseline];distribution=collections.Counter();iterations=6000
for i in range(iterations):
    c=dict(rng.choice(pool));nflip=1+rng.randrange(5)
    for n in rng.sample(names,nflip):
        if n=='q2':continue
        if n in c:
            del c[n]
        else:c[n]=-1 if n=='V2minusY2' else 1
    c=repair(c)
    if c is None:continue
    c=prune(c);ok,_,ob=run(c);assert ok and c.get('q2')==1
    distribution[14+len(c)]+=1
    score=lambda q:(len(q),len(run(q)[2]),sorted(q.items()))
    if score(c)<score(best):best=c
    if c not in pool:
        pool.append(c);pool.sort(key=score);pool=pool[:80]
ok,_,obligations=run(best);assert ok
out={'status':'PASS_BOUNDED_CONDITIONAL_SIGNED_CUT_SEARCH','iterations':iterations,'random_seed':20261106,'visited_states':len(cache),'baseline_witnesses':33,'best_witnesses':14+len(best),'best_cut_count':len(best),'best_cuts':dict(sorted(best.items())),'unproved_sign_obligations':obligations,'distribution':dict(sorted(distribution.items())),'scope':'Degree-only heuristic with each signed materialized gate assumed nonnegative except V2minusY2 assumed nonpositive; q2 stays positive-cut and qm/q stay inline for normalization. No sign proofs, concrete residual AST, model bridge, Lean theorem, endpoint, or optimality.'}
print(json.dumps(out,indent=2,sort_keys=True))
