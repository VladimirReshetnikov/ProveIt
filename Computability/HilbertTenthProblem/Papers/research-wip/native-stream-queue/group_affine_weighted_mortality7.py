#!/usr/bin/env python3
"""Seven-dimensional affine-input mortality using an asymmetric scalar.

Both the varying matrix and arbitrary-reset semantics are literal.  The
universal alphabet is abstract; finite fixtures are explicitly scoped.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

import group_affine_guarded_mortality9 as parent

gram=parent.gram
projective=parent.projective
reset4=parent.reset4
free=parent.parent.free
START4=(1,0,1,0)
ROW4=(1,0,1,0)
START=START4+(1,0,-2)
ROW=ROW4+(0,0,4)
RESET=reset4.outer(START,ROW)


def infinity_norm(matrix):return max(sum(abs(v) for v in row) for row in matrix)


def power(matrix,n):
    result=gram.ident(len(matrix))
    while n:
        if n&1:result=gram.mm(result,matrix)
        matrix=gram.mm(matrix,matrix);n//=2
    return result


def determinant(matrix):
    a=[list(row) for row in matrix];old=1;sign=1;n=len(a)
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];sign=-sign
        value=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*value-a[i][k]*a[k][j]
                assert numerator%old==0;a[i][j]=numerator//old
            a[i][k]=0
        old=value
    return sign*a[-1][-1]


def physical_input(t):
    return reset4.blocks((((0,-1),(1,t)),((0,-1),(t,t))))


def input_letter(t):
    return reset4.blocks((physical_input(t),parent.parent.scale01(parent.CT,t)))


def fixed_data(pair):
    P,Q=pair
    assert all(determinant(a)==1 for a in pair)
    scale=infinity_norm(P);assert scale>=1
    physical=reset4.blocks((P,reset4.scale(Q,scale)))
    growth=2*infinity_norm(physical)
    assert growth==2*infinity_norm(P)*infinity_norm(Q)
    return physical,scale,growth


def fixed_letter(pair):
    physical,_,growth=fixed_data(pair)
    return reset4.blocks((physical,reset4.scale(parent.CF,growth)))


def run(word,t,pairs):
    value=START
    for token in word:
        value=gram.mv(input_letter(t) if token==0 else fixed_letter(pairs[token]),value)
    return gram.dot(ROW,value)


def direct_profile(word,t,pairs):
    physical=START4;rho=1;n=0;fixed=0;inversions=0;Lambda=1
    paired=(gram.I2,gram.I2)
    for token in word:
        if token==0:
            matrix=physical_input(t);rho*=t;n+=1;inversions+=fixed
        else:
            matrix,scale,growth=fixed_data(pairs[token]);rho*=growth;fixed+=1;Lambda*=scale
            paired=tuple(gram.mm(a,b) for a,b in zip(pairs[token],paired))
        physical=gram.mv(matrix,physical)
    guard=n-2+3*inversions
    assert max(map(abs,physical))<=rho
    scalar=gram.dot(ROW4,physical)
    assert abs(scalar)<=2*rho
    return scalar,rho,guard,Lambda,paired


def power_checks():
    count=0
    for t in range(3,35):
        A=((0,-1),(1,t));B=((0,-1),(t,t))
        ap,bp=gram.I2,gram.I2
        aa,ab=0,1;ba,bb=0,1
        for k in range(65):
            if k:
                assert ap==((-aa,-ab),(ab,t*ab-aa))
                assert bp==((-t*ba,-bb),(t*bb,t*bb-t*ba))
                assert 0<=ab<=t**(k-1) and abs(bb)<=t**(k-1)
            else:assert ap==bp==gram.I2
            for value in (ap,bp):
                assert infinity_norm(value)<=2*t**k
                assert max(abs(value[0][0]),abs(value[1][0]))<=t**k
            ap=gram.mm(A,ap);bp=gram.mm(B,bp)
            if k:aa,ab=ab,t*ab-aa;ba,bb=bb,t*(bb-ba)
            count+=1
        assert determinant(A)==1 and determinant(B)==t
    B3=((0,-1),(3,3))
    assert power(B3,6)==reset4.scale(gram.I2,-27)
    # The tempting per-letter bound is false; only the run argument is used.
    assert infinity_norm(physical_input(3))==6>3
    return dict(exact_power_and_column_bounds=count,
                B3_sixth_power=power(B3,6),
                per_letter_bound_by_t_explicitly_false=True)


def input_checks():
    template=input_letter('input_t');assert len(template)==7
    assert {v for row in template for v in row}=={-1,0,1,'input_t'}
    assert gram.dot(ROW,START)==-6
    assert gram.mm(RESET,RESET)==reset4.scale(RESET,-6)
    cases=0
    for p in range(12):
        for x in (1,2,17,201):
            alpha,beta=12*2**(p+1),12*2**p
            source=parent.parent.loader(alpha,beta)
            t=gram.execute(source,dict(x=x))['input_t']
            assert gram.counts(source)==dict(M=1,A=1,operations=2)
            assert input_letter(t)==tuple(tuple(t if isinstance(v,str) else v for v in row)
                                         for row in template)
            assert determinant(input_letter(t))==t**4
            assert gram.mv(power(physical_input(t),2),START4)==(-1,t,-t,t*t)
            assert run((0,0),t,{})==-(t+1) and parent.run((0,0),t,{})==2
            cases+=1
    return dict(ordinary_program_input_cases=cases,input_matrix_template=template,
                input_loader=parent.parent.loader(),input_loader_counts=dict(M=1,A=1,operations=2),
                input_determinant='t^4',reset_square_multiplier=-6,
                changed_scalar_example='Two input letters alone give -(t+1), versus 2 in the9D series.')


def scalar_checks():
    U,B=projective.U,projective.B;I=gram.I2
    raw=((U,I),(gram.inv(U),I),(B,I),(gram.inv(B),I),
         (I,U),(I,gram.inv(U)),(I,B),(I,gram.inv(B)))
    pairs={i+1:pair for i,pair in enumerate(raw)}
    rng=random.Random(720263);valid=invalid=negative=dense=0
    for case in range(1536):
        t=rng.randrange(3,80)
        word=tuple(rng.randrange(9) for _ in range(rng.randrange(18)))
        if case%4==0:word=(0,0)+tuple(rng.randrange(1,9) for _ in range(rng.randrange(12)))
        scalar,rho,guard,Lambda,paired=direct_profile(word,t,pairs)
        result=run(word,t,pairs)
        assert result==scalar+4*rho*guard
        if guard:
            assert result!=0 and (result>0)==(guard>0);invalid+=1;negative+=guard<0
        else:
            assert word[:2]==(0,0) and all(word[2:])
            first,second=(gram.mv(a,(-1,t))[0] for a in paired)
            assert paired[0][0][0]%4==1 and abs(first)<t*Lambda
            assert scalar==first+t*Lambda*second
            assert (scalar==0)==(first==second==0);valid+=1
        if case<96:
            product_matrix=gram.ident(7)
            for token in word:
                matrix=input_letter(t) if token==0 else fixed_letter(pairs[token])
                product_matrix=gram.mm(matrix,product_matrix)
            assert gram.mm(gram.mm(RESET,product_matrix),RESET)==reset4.scale(RESET,result)
            dense+=1
    return dict(exact_arbitrary_word_scalar_cases=1536,valid_prefix_cases=valid,
                invalid_word_nonzeros=invalid,negative_guard_cases=negative,
                dense_reset_factorizations=dense)


def group_checks():
    accepted=wrong=bad_order=missing=separation=0
    for y in range(1,13):
        L,relator=free.shifted_a(y),free.defining_relator(y)
        left=free.multiply(free.inverse(free.A),L,free.A)
        by=free.multiply(free.inverse(free.A),free.inverse(L))
        witness=free.pair_witness(left,((by,0,-1),),2)
        assert reset4.fibre_pair(witness,(relator,))==(L,L)
        tokens=sorted(set(witness));ids={token:i+1 for i,token in enumerate(tokens)}
        pairs={ids[token]:reset4.pair_matrices(reset4.fibre_pair((token,),(relator,)))
               for token in tokens}
        suffix=tuple(ids[token] for token in reversed(witness));t=12*y+1
        assert run((0,0)+suffix,t,pairs)==0;accepted+=1
        assert run((0,0)+suffix,t+12,pairs)!=0;wrong+=1
        assert run((suffix[0],0,0)+suffix[1:],t,pairs)!=0;bad_order+=1
        assert run((0,)+suffix,t,pairs)!=0;missing+=1
    for y in range(1,25):
        r=12*y;t=r+1;L=projective.target(r);A=projective.U
        pairs={1:(L,gram.mm(gram.mm(gram.inv(A),L),A)),
               2:(gram.mm(gram.mm(A,L),gram.inv(A)),L)}
        s1=run((0,0,1),t,pairs);s2=run((0,0,2),t,pairs)
        assert s1 and s2 and not reset4.zero(reset4.scale(RESET,s1*s2));separation+=1
    # If first-block products may have p=0, the strict separation fails.
    rotation=((0,-1),(1,0));minusI=((-1,0),(0,-1))
    false=[]
    for t in (3,13,37):
        pair=(rotation,minusI);a,b=(gram.mv(M,(-1,t))[0] for M in pair)
        assert (a,b)==(-t,1) and run((0,0,1),t,{1:pair})==0
        false.append(dict(t=t,first=a,second=b,scalar=0))
    return dict(finite_one_relator_accepting_cases=accepted,same_word_wrong_input_nonzeros=wrong,
                wrong_prefix_order_nonzeros=bad_order,missing_input_nonzeros=missing,
                old_independent_bridge_nonzeros=separation,
                omitted_subgroup_hypothesis_counterexamples=false,
                universal_numerical_alphabet_instantiated=False)


def verify():
    return dict(status='PASS_GROUP_AFFINE_WEIGHTED_MORTALITY7',dimension=7,
                input_degree=1,input_loader_operations=2,varying_letters=1,
                fixed_alphabet='one per original signed paired letter, plus one constant rank-one reset',
                powers=power_checks(),input=input_checks(),scalars=scalar_checks(),groups=group_checks(),
                scope='Different zero-equivalent scalar from the rank-nine construction. '
                      'Unrestricted mortality over a fixed abstract universal alphabet, with one affine input letter. '
                      'Uniform arithmetic transfers through the existing paired-vector existence theorem; '
                      'no new numerical75/88 bound or arbitrary supplied-word certificate is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
