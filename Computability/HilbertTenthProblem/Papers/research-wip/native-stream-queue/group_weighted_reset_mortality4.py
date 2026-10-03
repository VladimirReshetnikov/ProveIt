#!/usr/bin/env python3
"""Four-dimensional unrestricted mortality with a three-operation reset.

The one varying matrix is a nonnegative rank-one quadratic reset. Fixed
letters are scaled paired group matrices, not a numerical universal table.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

import group_affine_weighted_mortality7 as parent

gram=parent.gram
projective=parent.projective
reset4=parent.reset4
free=parent.free
C=reset4.blocks((reset4.C,reset4.C))
ROW=(1,0,1,0)
TEMPLATE=((1,0,1,0),('t',0,'t',0),('t',0,'t',0),('t2',0,'t2',0))


def loader(alpha=24,beta=12):
    assert alpha>0 and beta>0
    return [('scaled','*',alpha,'x'),('t','+','scaled',beta+1),('t2','*','t','t')]


def column(t):return (1,t,t,t*t)


def reset(t):return reset4.outer(column(t),ROW)


def fixed_letter(pair):
    physical,_,_=parent.fixed_data(pair)
    return gram.mm(gram.mm(C,physical),C)


def word_matrix(word,pairs):
    value=gram.ident(4)
    for token in word:value=gram.mm(fixed_letter(pairs[token]),value)
    return value


def scalar(word,t,pairs):return gram.dot(ROW,gram.mv(word_matrix(word,pairs),column(t)))


def profile(word,t,pairs):
    P,Q=gram.I2,gram.I2;scale=1
    for token in word:
        pi,qi=pairs[token]
        P,Q=gram.mm(pi,P),gram.mm(qi,Q)
        scale*=parent.infinity_norm(pi)
    a,b=gram.mv(P,(-1,t))[0],gram.mv(Q,(-1,t))[0]
    return a,b,scale,P,Q


def separation_checks():
    count=equality=0
    for p,q,r,s in product(range(-6,7),repeat=4):
        if p*s-q*r!=1:continue
        P=((p,q),(r,s));norm=parent.infinity_norm(P)
        for t in (2,3,7,23):
            lhs=abs(-p+t*q);rhs=t*norm
            rotation=p==s==0 and q==-r and abs(q)==1
            assert lhs<=rhs and (lhs==rhs)==rotation
            count+=1;equality+=rotation
    H=((0,-1),(1,3))
    # Infinite-order cyclic illustration: trace>2; no claim of universality.
    for exponent in range(-12,13):
        P=parent.power(H if exponent>=0 else gram.inv(H),abs(exponent))
        for t in range(2,19):
            assert abs(gram.mv(P,(-1,t))[0])<t*parent.infinity_norm(P)
    return dict(sharp_SL2_inequality_cases=count,order_four_equality_cases=equality,
                cyclic_torsion_free_cases=25*17)


def input_checks():
    count=0
    for p in range(12):
        for x in (1,2,17,201):
            alpha,beta=12*2**(p+1),12*2**p
            source=loader(alpha,beta);env=gram.execute(source,dict(x=x));t=env['t'];R=reset(t)
            assert R==tuple(tuple(env[v] if isinstance(v,str) else v for v in row) for row in TEMPLATE)
            assert gram.counts(source)==dict(M=2,A=1,operations=3)
            assert all(v>=0 for row in R for v in row) and R[0][0]==1
            assert all(R[i][j]*R[k][ell]==R[i][ell]*R[k][j]
                       for i,j,k,ell in product(range(4),repeat=4))
            assert gram.mm(R,R)==reset4.scale(R,1+t)
            count+=1
    return dict(ordinary_input_cases=count,rank_one_16_entry_template=TEMPLATE,
                literal_source=loader(),loader_M=2,loader_A=1,loader_operations=3,
                reset_square_multiplier='1+t',matrix_entry_degree=2)


def arbitrary_word_checks():
    U,B,I=projective.U,projective.B,gram.I2
    raw=((U,I),(gram.inv(U),I),(B,I),(gram.inv(B),I),
         (I,U),(I,gram.inv(U)),(I,B),(I,gram.inv(B)),(U,B),(gram.inv(U),gram.inv(B)))
    pairs={i+1:pair for i,pair in enumerate(raw)}
    for pair in pairs.values():
        assert parent.determinant(fixed_letter(pair))==parent.infinity_norm(pair[0])**2
    rng=random.Random(420277);zeros=0
    for case in range(1536):
        t=rng.randrange(2,150)
        word=tuple(rng.randrange(1,11) for _ in range(rng.randrange(18)))
        a,b,scale,P,Q=profile(word,t,pairs);value=scalar(word,t,pairs)
        assert P[0][0]%4==1 and abs(a)<t*scale
        assert value==-(a+t*scale*b) and (value==0)==(a==b==0)
        R=reset(t);M=word_matrix(word,pairs)
        assert gram.mm(gram.mm(R,M),R)==reset4.scale(R,value)
        zeros+=value==0
    # Arbitrary invertible exterior words and zero to six resets.
    reset_cases=0
    for case in range(512):
        t=rng.randrange(2,80);R=reset(t);number=rng.randrange(7)
        words=[tuple(rng.randrange(1,11) for _ in range(rng.randrange(6))) for _ in range(number+1)]
        matrices=[word_matrix(w,pairs) for w in words]
        actual=matrices[0]
        for M in matrices[1:]:actual=gram.mm(M,gram.mm(R,actual))
        if not number:
            assert not reset4.zero(actual)
        else:
            interior=1
            for w in words[1:-1]:interior*=scalar(w,t,pairs)
            boundary=gram.mm(gram.mm(matrices[-1],R),matrices[0])
            assert actual==reset4.scale(boundary,interior)
            assert not reset4.zero(boundary)
            assert reset4.zero(actual)==(interior==0)
        reset_cases+=1
    rotation=((0,-1),(1,0));minusI=((-1,0),(0,-1))
    assert scalar((1,),13,{1:(rotation,minusI)})==0
    assert profile((1,),13,{1:(rotation,minusI)})[:2]==(-13,1)
    return dict(exact_word_scalar_and_two_reset_cases=1536,zero_scalar_cases=zeros,
                arbitrary_exterior_reset_cases=reset_cases,maximum_resets=6,
                missing_group_hypothesis_counterexample=True)


def group_checks():
    accepted=wrong=forced=separated=0
    for y in range(1,17):
        L,relator=free.shifted_a(y),free.defining_relator(y)
        left=free.multiply(free.inverse(free.A),L,free.A)
        by=free.multiply(free.inverse(free.A),free.inverse(L))
        witness=free.pair_witness(left,((by,0,-1),),2)
        assert reset4.fibre_pair(witness,(relator,))==(L,L)
        tokens=sorted(set(witness));ids={token:i+1 for i,token in enumerate(tokens)}
        pairs={ids[token]:reset4.pair_matrices(reset4.fibre_pair((token,),(relator,))) for token in tokens}
        word=tuple(ids[token] for token in reversed(witness));t=12*y+1
        M=word_matrix(word,pairs);R=reset(t)
        assert scalar(word,t,pairs)==0 and reset4.zero(gram.mm(gram.mm(R,M),R));accepted+=1
        assert scalar(word,t+12,pairs)!=0;wrong+=1
        # An accepting interior segment kills with arbitrary extra resets/exteriors.
        E=fixed_letter(next(iter(pairs.values())))
        value=gram.mm(E,gram.mm(R,gram.mm(M,gram.mm(R,gram.mm(E,R)))))
        assert reset4.zero(value);forced+=1
    for y in range(1,33):
        r=12*y;t=r+1;L=projective.target(r);A=projective.U
        pairs={1:(L,gram.mm(gram.mm(gram.inv(A),L),A)),
               2:(gram.mm(gram.mm(A,L),gram.inv(A)),L)}
        a,b=scalar((1,),t,pairs),scalar((2,),t,pairs)
        R=reset(t);M,N=fixed_letter(pairs[1]),fixed_letter(pairs[2])
        value=gram.mm(gram.mm(gram.mm(gram.mm(R,N),R),M),R)
        assert value==reset4.scale(R,a*b) and not reset4.zero(value);separated+=1
    return dict(finite_one_relator_accepting_words=accepted,wrong_input_nonzeros=wrong,
                accepting_interior_with_extra_reset_and_exteriors=forced,
                separate_one_block_bridges_nonzero=separated,
                numerical_universal_alphabet_instantiated=False)


def verify():
    return dict(status='PASS_GROUP_WEIGHTED_RESET_MORTALITY4',dimension=4,
                input_degree=2,input_loader_operations=3,varying_letters=1,
                fixed_alphabet='one scaled matrix per original signed paired generator',
                separation=separation_checks(),input=input_checks(),
                words=arbitrary_word_checks(),groups=group_checks(),
                scope='Unrestricted mortality is exactly the inherited paired endpoint; '
                      'the varying rank-one reset already loads both weighted vectors. '
                      'The sharp torsion-free separation lemma does not assert universality '
                      'for arbitrary torsion-free groups. No numerical75/88 improvement or '
                      'arbitrary supplied-word Diophantine certificate is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
