#!/usr/bin/env python3
"""Reproducible randomized, exhaustive, mutation, and arithmetic tests."""
import itertools
import json
import random
import time
from pathlib import Path
from profiles import (ExpPoly, Run, make_chain, build_profiles, verify_profiles,
                      brute_profile, restrict_profile, sign, profile_json, first_negative)
from compiler import compile_certificate


def compressed_signs(signs, infinite=False):
    out=[]
    for i,s in enumerate(signs):
        if out and out[-1].sign==s:
            out[-1]=Run(out[-1].lo,i,s)
        else:
            out.append(Run(i,i,s))
    if infinite:
        out[-1]=Run(out[-1].lo,None,out[-1].sign)
    return out


def main():
    start=time.time(); rng=random.Random(20261002); stats={}
    cases=1200
    for trial in range(cases):
        bases=rng.sample(range(1,7),rng.randint(1,3))
        shape={b:rng.randint(0,2) for b in bases}
        if sum(d+1 for d in shape.values())>7: continue
        terms={b:[rng.randint(-6,6) for _ in range(d+1)] for b,d in shape.items()}
        T=rng.randint(0,90)
        chain,_=make_chain(ExpPoly(terms),shape)
        finite=build_profiles(chain,T); infinite=build_profiles(chain,None)
        assert verify_profiles(chain,finite,T)
        assert verify_profiles(chain,infinite,None)
        for j,f in enumerate(chain):
            expected=brute_profile(f,T)
            assert finite[j]==expected
            assert restrict_profile(infinite[j],T)==expected
        stats['random_shapes_checked']=stats.get('random_shapes_checked',0)+1
    # Finite and infinite uniqueness among every sign sequence on 0,...,6.
    f=ExpPoly({1:[64],2:[-20],4:[1]}); shape={1:0,2:0,4:0}
    chain,_=make_chain(f,shape)
    for T in (6,None):
        actual=build_profiles(chain,T); accepted=0; tested=0
        for ss in itertools.product((-1,0,1),repeat=7):
            rows=compressed_signs(ss,T is None)
            if len(rows)>5: continue
            candidate=[rows]+actual[1:]
            tested+=1
            if verify_profiles(chain,candidate,T):
                accepted+=1
                assert candidate==actual
        assert accepted==1
        stats['exhaustive_'+('infinite' if T is None else 'finite')]={'candidates':tested,'accepted':accepted}
    # Compiler parameter uniformity, including zero polynomials and zero horizon.
    shape={1:0,2:0,4:0}; signatures={}
    for terms in ({1:[64],2:[-20],4:[1]}, {1:[0],2:[0],4:[0]}, {1:[-2],2:[3],4:[-1]}):
        for T in (0,6,31,None):
            c,_=compile_certificate(terms,shape,T)
            assert c.valid()
            m=c.metadata(); sig=tuple(m[k] for k in ('variables','inputs','witnesses','quadratic_residuals','power_atoms'))
            mode='infinite' if T is None else 'finite'
            if mode in signatures: assert signatures[mode]==sig
            signatures[mode]=sig
    stats['parametric_compiler_instances']=12
    stats['parameter_independent_signatures']=signatures
    # Every individual witness coordinate is constrained (this is not a uniqueness proof).
    mutations=0
    for T in (6,None):
        c,_=compile_certificate({1:[64],2:[-20],4:[1]},shape,T)
        for i,role in enumerate(c.roles):
            if role!='witness': continue
            v=list(c.values); v[i]+=1
            assert not c.valid(v),(T,i,c.names[i])
            mutations+=1
    stats['single_coordinate_mutants_rejected']=mutations
    # Random repeated-root compiler instances.
    for _ in range(16):
        shape={2:rng.randint(0,2),3:0}
        terms={b:[rng.randint(-5,5) for _ in range(d+1)] for b,d in shape.items()}
        T=rng.choice([0,12,None]); c,_=compile_certificate(terms,shape,T)
        assert c.valid()
    stats['additional_compiler_instances']=16
    # Exact large-horizon isolated defect, without scanning its 100,001 points.
    K=50000; T=100000
    big=ExpPoly({2:[K*K-1,-2*K,1]}); bc,_=make_chain(big,{2:2})
    bp=build_profiles(bc,T)
    construction_evals=sum(x.evaluations for x in bc)
    assert verify_profiles(bc,bp,T)
    assert first_negative(bp[0])==K
    assert [r for r in bp[0] if r.sign==0]==[Run(K-1,K-1,0),Run(K+1,K+1,0)]
    stats['large_horizon']={'T':T,'first_negative':K,'stored_runs':sum(map(len,bp)),
                           'construction_evaluations':construction_evals,
                           'evaluations_including_verification':sum(x.evaluations for x in bc),
                           'base_power_bits_at_T':pow(2,T).bit_length(),
                           'profiles':profile_json(bp)}
    # Sharp bound: polynomial roots at every second integer, times 2**n.
    sharp=[]
    for d in range(0,7):
        co=[1]
        for r in range(1,d+1):
            nxt=[0]*(len(co)+1)
            for k,a in enumerate(co): nxt[k]-=2*r*a; nxt[k+1]+=a
            co=nxt
        sc,_=make_chain(ExpPoly({2:co}),{2:d})
        sp=build_profiles(sc,2*d+2)
        assert len(sp[0])==2*(d+1)-1
        assert verify_profiles(sc,sp,2*d+2)
        sharp.append({'order':d+1,'runs':len(sp[0])})
    stats['sharp_bound_examples']=sharp
    # Rational rotation: integer recurrence for Re((3+4i)**n), no floating point.
    x,y=1,0; ss=[]
    for n in range(1001):
        ss.append(sign(x)); x,y=3*x-4*y,4*x+3*y
    assert 0 not in ss
    stats['rotation_sign_changes_through_1000']=sum(a!=b for a,b in zip(ss,ss[1:]))
    stats['elapsed_seconds']=round(time.time()-start,3)
    target=Path(__file__).resolve().parent.parent/'data'/'test_results.json'
    target.write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))


if __name__=='__main__': main()
