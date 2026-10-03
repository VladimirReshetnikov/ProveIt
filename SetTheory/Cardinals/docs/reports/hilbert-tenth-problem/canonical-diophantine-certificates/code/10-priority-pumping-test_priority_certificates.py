#!/usr/bin/env python3
"""Reproducible finite checks; these complement, and do not replace, proofs."""
from __future__ import annotations
import itertools
import json
import random
import time
from pathlib import Path
from priority_certificates import (Circuit, Poly, compile_block, as_inputs, from_fractions,
                                  affine_interval, block_valid, unroll, infinite_word,
                                  maximal_blocks, step, repetition_capacity, least_seed_for_repetitions)

def run_tests() -> dict:
    rng=random.Random(20260930)
    counts={}
    t0=time.perf_counter()
    # Independently enumerate candidate witnesses for the two nontrivial gates.
    c=Circuit(); u=c.input('u');v=c.input('v');c.lt(u,v)
    n=0
    for a in range(9):
        for b in range(9):
            solutions=[]
            for bit in range(3):
                for slack in range(11):
                    vals=[a,b,bit,slack]
                    if c.value(vals)==0: solutions.append((bit,slack))
            expected=(int(a<b),b-a-1 if a<b else a-b)
            assert solutions==[expected],(a,b,solutions)
            n+=1
    counts['comparison_unique_fibres_exhaustive']=n
    c=Circuit(); a=c.input('a');d=c.input('d');c.div(a,d)
    n=0
    for av in range(13):
        for dv in range(1,7):
            sols=[]
            for q in range(14):
                for r in range(7):
                    for s in range(7):
                        if c.value([av,dv,q,r,s])==0: sols.append((q,r,s))
            q,r=divmod(av,dv)
            assert sols==[(q,r,dv-r-1)]
            n+=1
    counts['division_unique_fibres_exhaustive']=n
    n=0
    for a in range(-15,16):
        for slope in range(-7,8):
            for k in range(15):
                lo,hi=affine_interval(a,slope,k)
                actual=[h for h in range(k) if a+h*slope>=0]
                assert list(range(lo,hi))==actual,(a,slope,k,lo,hi,actual)
                n+=1
    counts['affine_interval_exhaustive']=n
    # Exhaustive one-counter two-rule priority programs and short words.
    n=0
    words=[(0,),(1,),(0,1),(1,0),(1,1)]
    for a0,b0,a1,b1 in itertools.product(range(3),repeat=4):
        A=[[a0],[a1]];B=[[b0],[b1]]
        for x in range(5):
            for word in words:
                for k in range(6):
                    direct,_=unroll(A,B,[x],word,k)
                    assert block_valid(A,B,[x],word,k)==direct
                    n+=1
    counts['one_counter_blocks_exhaustive']=n
    n=0
    for _ in range(12000):
        m=rng.randint(1,5);d=rng.randint(1,5);ell=rng.randint(1,5)
        A=[[rng.randrange(4) for _ in range(d)] for _ in range(m)]
        B=[[rng.randrange(4) for _ in range(d)] for _ in range(m)]
        x=[rng.randrange(12) for _ in range(d)]
        word=[rng.randrange(m) for _ in range(ell)];k=rng.randrange(15)
        direct,_=unroll(A,B,x,word,k)
        assert block_valid(A,B,x,word,k)==direct
        if infinite_word(A,B,x,word):
            assert unroll(A,B,x,word,100)[0]
        n+=1
    counts['random_multicounter_blocks']=n
    # Construct actual quartic certificates, both true and false instances.
    n=mutations=0
    examples=[]
    for m,d,word in [(1,1,[0]),(2,2,[1]),(3,2,[1,2,0]),(4,3,[3,1])]:
        c=compile_block(m,d,word,endpoint=True)
        examples.append({'m':m,'d':d,'word_zero_based':word,**c.stats()})
        for _ in range(160):
            A=[[rng.randrange(4) for _ in range(d)] for _ in range(m)]
            B=[[rng.randrange(4) for _ in range(d)] for _ in range(m)]
            x=[rng.randrange(12) for _ in range(d)];k=rng.randrange(12)
            valid,ytrue=unroll(A,B,x,word,k)
            delta=[sum(A[j][p]-B[j][p] for j in word) for p in range(d)]
            y=[max(0,x[p]+k*delta[p]) for p in range(d)]
            vals=c.witness(as_inputs(A,B,x,k,y))
            assert c.value(vals,include_obligations=False)==0
            assert (c.value(vals)==0)==valid
            assert c.accept.evaluate(vals)==int(valid)
            if valid:
                assert tuple(y)==ytrue
            # Each single-coordinate auxiliary corruption must fail a gate.
            aux=[i for i in range(len(c.names)) if i not in c.inputs.values()]
            for i in rng.sample(aux,min(5,len(aux))):
                vals[i]+=1
                assert c.value(vals,include_obligations=False)>0
                vals[i]-=1;mutations+=1
            n+=1
    counts['actual_polynomial_instances']=n
    counts['single_auxiliary_mutation_rejections']=mutations
    # Interior-only priority conflict: endpoints of the proposed block pass.
    primes,A,B=from_fractions([(1,72),(3,2)])
    x=[5,0];word=[1];k=5
    assert all(not all(x[p]+h*(-1 if p==0 else 1)>=B[0][p]
                       for p in range(2)) for h in [0,4])
    assert maximal_blocks(A,B,x,word)==2
    assert not block_valid(A,B,x,word,k)
    mc=compile_block(2,2,[1],endpoint=True,maximal=True)
    vals=mc.witness(as_inputs(A,B,x,2,[3,2]));assert mc.value(vals)==0
    bad=mc.witness(as_inputs(A,B,x,1,[4,1]));assert mc.value(bad)>0
    counts['interior_priority_and_maximality_checks']=5
    # Gigantic exact horizon: no unrolling.
    primes,A,B=from_fractions([(3,2)])
    sizes=[]
    for exponent in [1,10,100,1000]:
        k=10**exponent;x=[k,7];y=[0,k+7]
        c=compile_block(1,2,[0],endpoint=True,maximal=True)
        vals=c.witness(as_inputs(A,B,x,k,y));assert c.value(vals)==0
        sizes.append({'k':'10^'+str(exponent),'maximum_witness_bits':max(vals).bit_length(),**c.stats()})
    counts['giant_horizon_certificates']=4
    # Two-phase doubling: exact native fraction interpreter vs valuation one.
    fracs=[(33,10),(5,11),(7,5),(52,21),(7,13),(5,7)]
    primes,A,B=from_fractions(fracs)
    def encoded(exps):
        out=1
        for p,v in zip(primes,exps): out*=p**v
        return out
    phase=[];n=10;x=[1 if p in [2,5] else 0 for p in primes]
    for round_index in range(7):
        a=2**round_index
        expected=[0,1]*a+[2]+[3,4]*a+[5]
        observed=[]
        for label in expected:
            st=step(A,B,x);assert st is not None and st[0]==label
            next_n=None; chosen=None
            for i,(num,den) in enumerate(fracs):
                if n*num%den==0: chosen=i;next_n=n*num//den;break
            assert chosen==label
            x=list(st[1]);n=next_n;assert encoded(x)==n
            observed.append(label)
        target=[2*a if p==2 else 1 if p==5 else 0 for p in primes]
        assert x==target
        phase.append({'round':round_index,'a':a,'steps':len(expected),
                      'next_exponent_of_2':2*a})
    counts['doubling_native_integer_steps']=sum(p['steps'] for p in phase)
    # Repetition capacity, minimal-seed theorem and sharp 2H pumping bound.
    n=0
    for _ in range(8000):
        m=rng.randrange(1,5);d=rng.randrange(1,5)
        A=[[rng.randrange(5) for _ in range(d)] for _ in range(m)]
        B=[[rng.randrange(5) for _ in range(d)] for _ in range(m)]
        word=[rng.randrange(m) for _ in range(rng.randrange(1,5))]
        cap,least,delta=repetition_capacity(A,B,word)
        H=max(map(max,B))
        assert cap is None or cap<=2*H
        for k in range(1,2*H+4):
            seed=least_seed_for_repetitions(A,B,word,k)
            predicted=cap is None or k<=cap
            assert unroll(A,B,seed,word,k)[0]==predicted
            # Raising the seed cannot repair a priority failure.
            larger=[v+rng.randrange(4) for v in seed]
            if unroll(A,B,larger,word,k)[0]: assert predicted
            n+=1
        assert infinite_word(A,B,least,word)==(cap is None and all(s>=0 for s in delta))
    counts['capacity_minimal_seed_and_pumping_instances']=n
    sharp=[]
    for H in range(1,13):
        primes,A,B=from_fractions([(1,7*6**H),(7,10),(15,7)])
        cap,least,delta=repetition_capacity(A,B,[1,2])
        assert cap==2*H
        for k in [2*H,2*H+1]:
            seed=least_seed_for_repetitions(A,B,[1,2],k)
            assert unroll(A,B,seed,[1,2],k)[0]==(k==2*H)
        sharp.append({'H':H,'capacity':cap})
    counts['sharp_bound_family_instances']=12
    # Formula for variable/residual accounting, independently sampled shapes.
    for m in range(1,5):
        for d in range(1,4):
            for ell in range(1,4):
                word=[rng.randrange(m) for _ in range(ell)]
                c=compile_block(m,d,word,endpoint=True)
                R=sum(j+1 for j in word);S=d*R
                st=c.stats()
                # Constants obtained from a transparent gate-by-gate count.
                assert st['auxiliary_variables']==29*S+3*d*ell+12*d+3*R+3*ell
                assert st['quadratic_residuals']==32*S+3*d*ell+15*d+4*R+4*ell+1
    counts['exact_size_formula_shapes']=36
    return {'seed':20260930,'status':'all checks passed','counts':counts,
            'total_counted_checks':sum(counts.values()),'circuit_examples':examples,
            'giant_horizons':sizes,'doubling_rounds':phase,'sharp_capacity_examples':sharp,
            'elapsed_seconds':round(time.perf_counter()-t0,3),
            'scope':'Finite tests are not a formal proof or an exhaustive test of all inputs.'}

if __name__=='__main__':
    result=run_tests()
    out=Path(__file__).resolve().parent.parent/'results'/'verification.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
