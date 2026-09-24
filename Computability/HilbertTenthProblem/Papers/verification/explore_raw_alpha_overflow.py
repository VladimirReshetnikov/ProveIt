#!/usr/bin/env python3
"""General pre-mask/overflow lemma; not the remaining alpha-deletion proof."""
from pathlib import Path
import json
import sympy as sp
from explore_native_ternary_ripple import central_valuation


def symbolic():
    q,W,J=sp.symbols('q W J')
    a_bound=(W*(3*J-2)-2)/(W-1)
    assert sp.factor(a_bound-(3*J-2+(3*J-4)/(W-1)))==0
    upper=sp.Rational(3,2)*q**6+4*q*sum(q**i for i in range(5))
    gap=(q**6*(q-9)+8*q)/(2*(q-1))
    assert sp.factor(2*q**6-upper-gap)==0
    z=sp.Symbol('z')
    numerator=sp.Poly(sp.expand((q**6*(q-9)+8*q).subs(q,z+9)),z)
    assert all(c>0 for c in numerator.all_coeffs())
    fmax=sp.Rational(13,2)*(q-1)/2-5
    gmax=sp.Rational(15,2)*(q-1)/2-5
    margins=[sp.expand(4*q-fmax-3),sp.expand(4*q-gmax-3)]
    assert margins==[3*q/4+sp.Rational(21,4),q/4+sp.Rational(23,4)]
    assert sp.factor((8*W-2)/(W-1)-(8+6/(W-1)))==0
    return dict(packing_gap=sp.sstr(gap),gap_numerator_coefficients_at_q_equals_z_plus_9=list(map(str,numerator.all_coeffs())),
                carry_margins=list(map(sp.sstr,margins)),
                scope='Exact symbolic identities; sign conditions q>=9,W>=3,J>=4 are proved in the note from positive source equations.')


def regression():
    words=accepted=chunks=small=0;min_margin=None
    for N in range(2,10):
        L=3**N
        for P in range(L,2*L):
            words+=1
            if central_valuation(P)<N:continue
            accepted+=1
            # Independently reconstruct every ternary carry, including top1.
            value=P;carry=0;carries=[]
            for place in range(N+1):
                value,digit=divmod(value,3)
                carry=int(2*digit+carry>=3);carries.append(carry)
            assert value==0 and sum(carries)>=N
            assert carries[-2:]==[1,1] and carries.count(0)<=1
            for ell in range(1,N+1):
                q=3**ell;J=(q-1)//2
                chunk=P//3**(N-ell)%q
                assert chunk>=J
                chunks+=1
                margin=chunk-J
                min_margin=margin if min_margin is None else min(min_margin,margin)
    for S in range(2,20):
        for f0 in range(1,S):
            f1=S-f0
            for T in range(1,5):
                fields=[2,f0+T,f0,f1+T,f1]
                carry=0
                for field in fields:carry=(field+carry)//9
                assert carry<=2
                small+=1
    for q in (9,27,81,243):
        for kp in (1,2):
            value=kp;carry=0;arr=[]
            for place in range(2 if kp==1 else 3):
                value,digit=divmod(value,3);carry=int(2*digit+carry>=3);arr.append(carry)
            if kp==1 or q>=27:assert arr.count(0)>=2
    return dict(overflow_words=words,accepted_maximal_valuation_words=accepted,
                highest_chunk_checks=chunks,minimum_chunk_minus_repunit=min_margin,
                q9_track_split_and_top_mask_cases=small,
                scope='Complete overflow words for2<=N<=9, every top-chunk length1..N; allpositive q9 track splits withS<=19 andT<=4. These supplement the general proof only.')


def verify():
    return dict(status='PASS_RAW_ALPHA_OVERFLOW_LEMMA',symbolic=symbolic(),regression=regression(),
                proof='../1980/EXPLORATION_RAW_ALPHA_OVERFLOW_LEMMA.md',
                scope='Proves pre-power kernel ranges and excludes P>=q6 without aggregatealpha. Does not claim the remaining supplied-field recovery, the oldS<=3J bound, or a complete smaller certificate.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['regression'])
