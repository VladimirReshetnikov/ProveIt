"""Deterministic finite regressions for the report. These are not model/proof certificates."""
from __future__ import annotations
from pathlib import Path
import json
import random
import time
from syntax import *
from test_reference import identity

ROOT=Path(__file__).resolve().parents[1]

def output(rows: tuple[int,...], s: int) -> int:
    r=0
    while s:
        low=s&-s; r |= rows[low.bit_length()-1]; s^=low
    return r

def positive_orbit(rows: tuple[int,...], seed: int) -> int:
    c=0
    while True:
        new=c|output(rows,c|seed)
        if new==c: return c
        c=new

def graph_audit() -> dict:
    graph_count=seed_count=coverage_graphs=bootstrap_roots=0
    for n in range(1,5):
        full=(1<<n)-1
        for code in range(1<<(n*n)):
            rows=tuple((code>>(n*i))&full for i in range(n))
            graph_count+=1
            global_range=output(rows,full)
            for seed in range(1<<n):
                c=positive_orbit(rows,seed); seed_count+=1
                assert output(rows,c|seed)&~c==0
                assert c&~global_range==0
                # An independent path-length construction, with n positive stages.
                stage=seed; d=0
                for _ in range(n): stage=output(rows,stage); d|=stage
                assert d==c
            # Now reinterpret rows[x] as the members of x, not arbitrary rho outputs.
            active=global_range
            singleton_represented=0
            for r in rows:
                if r and r&(r-1)==0: singleton_represented|=r
            if active&~singleton_represented: continue
            coverage_graphs+=1
            switch=[]
            for x in range(n):
                if rows[x] and rows[x]&(rows[x]-1)==0:
                    switch.append(rows[x]) # the one unique member
                else:
                    switch.append(sum(1<<y for y in range(n) if rows[y]&~rows[x]==0))
            switch=tuple(switch)
            for root in range(n):
                c=positive_orbit(switch,1<<root); bootstrap_roots+=1
                assert rows[root]&~c==0 # root is only an input seed, not required in c
                assert output(rows,c)&~c==0 # transitivity
                for y in range(n):
                    if rows[root]>>y&1: assert rows[y]&~c==0 # subset bound for members of root
    return dict(graphs=graph_count,relation_seed_pairs=seed_count,
                singleton_coverage_graphs=coverage_graphs,bootstrap_roots=bootstrap_roots)

def metrics() -> dict:
    h=('H',0,1)
    ans={}
    for label,seed,base in [('point','point','ext'),('subset','subset','ext'),('equality_free','subset','ec')]:
        old=extensionality('old') if base=='ext' else congruence('old')
        short=extensionality() if base=='ext' else congruence()
        ans[label]={
          'old_mixed':nodes(old)+nodes(closure(h,seed=seed,mixed=True,curried=False)),
          'pure_only':nodes(old)+nodes(closure(h,seed=seed,curried=False)),
          'pure_curried':nodes(old)+nodes(closure(h,seed=seed)),
          'pure_curried_directed':nodes(short)+nodes(closure(h,seed=seed))}
    ans['scope']='Occurrence tree in {E, equality, bottom, implication, forall}; each matrix hole costs 1. No variable payloads, arbitrary parameter closure, logical rules, or backend cost. No state counts.'
    ans['components']={'old_ext':nodes(extensionality('old')),'short_ext':nodes(extensionality()),
          'old_ec':nodes(congruence('old')),'short_ec':nodes(congruence()),
          'proposed_schema':nodes(closure(h))}
    return ans

def codec_audit() -> dict:
    for n in range(100000):
        f=decode(n)
        assert not labels(f) if n==0 else all(v<n for v in labels(f))
        canonical=encode(f)
        assert canonical<=n
        assert decode(canonical)==f
    rng=random.Random(20261016)
    tests=0
    for _ in range(3000):
        x,y=rng.randrange(10000),rng.randrange(10000)
        assert unpair(pair(x,y))==(x,y)
        # Constructor decoding commutes with the single harmless truth-fold.
        assert decode(4*pair(x,y))==smart_imp(decode(x),decode(y))
        tests+=1
    return {'raw_codes':100000,'constructor_pair_checks':tests,'bottom_code':1,'self_membership_code':3}

def rand_formula(rng: random.Random, depth: int) -> Formula:
    if depth==0 or rng.randrange(4)==0: return E(rng.randrange(4),rng.randrange(4))
    if rng.randrange(3)==0: return A(rng.randrange(4),rand_formula(rng,depth-1))
    return I(rand_formula(rng,depth-1),rand_formula(rng,depth-1))

def semantic_audit() -> dict:
    congruence_cases=0
    for n in range(1,4):
        mask=(1<<n)-1
        for c in range(1<<(n*n)):
            mem=tuple((c>>(n*i))&mask for i in range(n))
            assert evaluate(congruence('old'),mem,{})==evaluate(congruence(),mem,{})
            assert evaluate(extensionality('old'),mem,{})==evaluate(extensionality(),mem,{})
            congruence_cases+=1
    rng=random.Random(8675309)
    substitutions=curried=0
    for _ in range(1000):
        n=rng.randrange(1,4); mem=tuple(rng.randrange(1<<n) for _ in range(n))
        f=rand_formula(rng,4); x,y=rng.randrange(4),rng.randrange(4)
        env={i:rng.randrange(n) for i in range(4)}
        assert evaluate(subst(f,{x:y}),mem,env)==evaluate(f,mem,env|{x:env[y]})
        substitutions+=1
    # Small domains make full schema-wrapper evaluation inexpensive.
    matrices=[E(0,1),I(E(0,2),E(2,1)),A(0,E(0,1)),I(E(1,0),B)]
    for n in (1,2):
        for c in range(1<<(n*n)):
            mem=tuple((c>>(n*i))&((1<<n)-1) for i in range(n))
            for matrix in matrices:
                assert evaluate(closure(matrix,curried=False),mem,{})==evaluate(closure(matrix),mem,{})
                curried+=1
    return dict(congruence_and_extensionality_structures=congruence_cases,
                capture_avoiding_substitutions=substitutions,curried_schema_checks=curried)

def main() -> None:
    start=time.monotonic()
    result={'graph':graph_audit(),'codec':codec_audit(),'semantics':semantic_audit(),
            'metrics':metrics(),'status':'all assertions passed',
            'limitations':'Finite regressions only. No Lean/Coq build, proof compiler, TM table, or state bound.'}
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    (ROOT/'data'/'experiments.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'data'/'metrics.json').write_text(json.dumps(result['metrics'],indent=2)+'\n')
    (ROOT/'data'/'identity.json').write_text(json.dumps(identity(E(0,0)),indent=2)+'\n')
    (ROOT/'data'/'schema_example.json').write_text(json.dumps([['PSC',E(0,1)]],indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    if not __debug__: raise SystemExit('Run without -O: assertions implement the regressions')
    main()
