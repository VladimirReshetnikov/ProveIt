#!/usr/bin/env python3
"""An affine, two-gate input for unrestricted ten-dimensional mortality.

All words are chronological: a later letter multiplies on the left.
The universal fixed alphabet is inherited abstractly, not instantiated here.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

import group_gram_zero_mortality as gram
import group_projective_zero_mortality6 as projective
import group_two_reset_mortality4 as reset4
import group_commutator_universal_substrate as free


CONTROL_INPUT = ((1,0,0,0),(1,1,0,0),(0,0,1,0),(0,0,1,1))
CONTROL_FIXED = ((1,0,0,0),(0,1,0,0),(1,0,1,0),(0,0,0,1))
CONTROL_ROW = (-2,1,0,3)
PHYSICAL_START = (1,0,0,1,0,0)
WEIGHTS = (1,2,3,1,2,3)
START = PHYSICAL_START+(1,0,0,0)
ROW = projective.ROW+tuple(4*x for x in CONTROL_ROW)
RESET = reset4.outer(START,ROW)


def scale01(a,c):
    """Copies only, also supporting the symbolic input register template."""
    assert all(x in (0,1) for row in a for x in row)
    return tuple(tuple(c if x else 0 for x in row) for row in a)


def physical_input(t):
    block=((0,0,1),(t,1,0),(1,t,0))
    return reset4.blocks((block,block))


def input_letter(t):
    return reset4.blocks((physical_input(t),scale01(CONTROL_INPUT,t)))


def weighted_bound(a):
    return max((sum(abs(x)*weight for x,weight in zip(row,WEIGHTS))+denominator-1)//denominator
               for row,denominator in zip(a,WEIGHTS))


def fixed_letter(a):
    assert len(a)==6 and all(len(row)==6 for row in a)
    bound=weighted_bound(a)
    assert bound>=1
    return reset4.blocks((a,scale01(CONTROL_FIXED,bound)))


def loader(alpha=24,beta=12):
    assert alpha>0 and beta>0
    return [('scaled','*',alpha,'x'),('input_t','+','scaled',beta+1)]


def run(word,t,physical):
    """Token zero is the sole variable letter; positive tokens are fixed."""
    vector=START
    for token in word:
        matrix=input_letter(t) if token==0 else fixed_letter(physical[token])
        vector=gram.mv(matrix,vector)
    return gram.dot(ROW,vector)


def direct_profile(word,t,physical):
    n=word.count(0)
    f=len(word)-n
    inversions=sum(word[i]!=0 and word[j]==0
                   for i in range(len(word)) for j in range(i+1,len(word)))
    guard=n-2+3*inversions
    growth=t**n
    state=PHYSICAL_START
    for token in word:
        a=physical_input(t) if token==0 else physical[token]
        state=gram.mv(a,state)
        if token: growth*=weighted_bound(a)
    scalar=gram.dot(projective.ROW,state)
    assert all(abs(value)<=growth*weight for value,weight in zip(state,WEIGHTS))
    return (1,n,f,inversions),guard,growth,scalar


def control_checks():
    count=valid=0
    for length in range(12):
      for word in product((0,1),repeat=length):
        state=(1,0,0,0)
        for token in word:
            state=gram.mv(CONTROL_INPUT if token==0 else CONTROL_FIXED,state)
        n=word.count(0)
        inv=sum(word[i]==1 and word[j]==0
                for i in range(length) for j in range(i+1,length))
        assert state==(1,n,length-n,inv)
        guard=gram.dot(CONTROL_ROW,state)
        intended=len(word)>=2 and word[:2]==(0,0) and all(word[2:])
        assert (guard==0)==intended
        valid+=intended;count+=1
    return dict(exhaustive_binary_control_words=count,valid_prefix_words=valid,
                control_matrices_have_only_zero_one_entries=True)


def input_checks():
    rng=random.Random(142021);cases=0
    template=input_letter('input_t')
    assert {x for row in template for x in row}=={0,1,'input_t'}
    assert gram.dot(ROW,START)==-6
    assert gram.mm(RESET,RESET)==reset4.scale(RESET,-6)
    minimum=gram.execute(loader(1,1),{'x':1})['input_t']
    assert minimum==3 and weighted_bound(physical_input(minimum))==minimum
    assert weighted_bound(physical_input(2))>2  # The strict domain t>=3 matters.
    for _ in range(512):
        p=rng.randrange(24);x=rng.randrange(1,200)
        alpha,beta=12*2**(p+1),12*2**p
        source=loader(alpha,beta)
        env=gram.execute(source,dict(x=x));t=env['input_t']
        assert gram.counts(source)==dict(M=1,A=1,operations=2)
        assert t==alpha*x+beta+1 and t>=3
        actual=input_letter(t)
        assert actual==tuple(tuple(env[v] if isinstance(v,str) else v for v in row)
                            for row in template)
        T=physical_input(t)
        assert gram.mv(T,gram.mv(T,PHYSICAL_START))==projective.column(t)
        block=((0,0,1),(t,1,0),(1,t,0))
        determinant=(block[0][0]*(block[1][1]*block[2][2]-block[1][2]*block[2][1])
                    -block[0][1]*(block[1][0]*block[2][2]-block[1][2]*block[2][0])
                    +block[0][2]*(block[1][0]*block[2][1]-block[1][1]*block[2][0]))
        assert determinant==t*t-1>0
        assert all(value<=t*weight for value,weight in zip(gram.mv(T,WEIGHTS),WEIGHTS))
        assert weighted_bound(T)<=t
        cases+=1
    return dict(ordinary_program_input_cases=cases,source=loader(),
                source_counts=gram.counts(loader()),input_matrix_template=template,
                full_input_determinant='t^4*(t^2-1)^2',constant_reset_square_multiplier=-6,
                minimum_positive_affine_input=minimum,weighted_norm_domain_boundary_checked=True)


def scalar_checks():
    rng=random.Random(141443);cases=dense=valid=invalid=negative_guard=0
    A=((1,1),(0,1));B=((1,0),(1,1));I=gram.I2
    pairs=((A,I),(gram.inv(A),I),(B,I),(gram.inv(B),I),
           (I,A),(I,gram.inv(A)),(I,B),(I,gram.inv(B)))
    physical={i+1:projective.lift(pair) for i,pair in enumerate(pairs)}
    for case in range(1024):
        t=rng.randrange(3,64)
        word=tuple(rng.randrange(9) for _ in range(rng.randrange(14)))
        if case%4==0:
            word=(0,0)+tuple(rng.randrange(1,9) for _ in range(rng.randrange(10)))
        state,guard,growth,scalar=direct_profile(word,t,physical)
        actual=run(word,t,physical)
        assert abs(scalar)<=2*growth
        assert actual==scalar+4*growth*guard
        if guard:
            assert actual!=0 and (actual>0)==(guard>0)
            invalid+=1;negative_guard+=guard<0
        else:
            assert word[:2]==(0,0) and all(word[2:])
            pair=(I,I)
            for token in word[2:]:
                pair=tuple(gram.mm(a,b) for a,b in zip(pairs[token-1],pair))
            direct=sum(gram.mv(a,(-1,t))[0]**2 for a in pair)
            assert actual==scalar==direct
            valid+=1
        if case<96:
            product_matrix=gram.ident(10)
            for token in word:
                a=input_letter(t) if token==0 else fixed_letter(physical[token])
                product_matrix=gram.mm(a,product_matrix)
            assert gram.dot(ROW,gram.mv(product_matrix,START))==actual
            assert gram.mm(gram.mm(RESET,product_matrix),RESET)==reset4.scale(RESET,actual)
            dense+=1
        cases+=1
    return dict(exact_scalar_and_domination_cases=cases,valid_guard_cases=valid,
                invalid_guard_nonzeros=invalid,negative_guard_nonzeros=negative_guard,
                independent_dense_product_and_rank_one_cases=dense)


def group_checks():
    accepted=wrong=bad_order=one_input=0
    for y in range(1,13):
        L,relator=free.shifted_a(y),free.defining_relator(y)
        left=free.multiply(free.inverse(free.A),L,free.A)
        by=free.multiply(free.inverse(free.A),free.inverse(L))
        witness=free.pair_witness(left,((by,0,-1),),2)
        pair=reset4.fibre_pair(witness,(relator,))
        assert pair==(L,L)
        alphabet=sorted(set(witness))
        ids={token:i+1 for i,token in enumerate(alphabet)}
        physical={ids[token]:projective.lift(reset4.pair_matrices(reset4.fibre_pair((token,),(relator,))))
                  for token in alphabet}
        # Existing free words multiply on the right; chronological words reverse them.
        suffix=tuple(ids[token] for token in reversed(witness))
        word=(0,0)+suffix;t=12*y+1
        assert run(word,t,physical)==0;accepted+=1
        assert run(word,t+12,physical)>0;wrong+=1
        assert run((0,)+suffix,t,physical)!=0;one_input+=1
        assert run((suffix[0],0,0)+suffix[1:],t,physical)!=0;bad_order+=1
    separation=0
    for y in range(1,25):
        r=12*y;t=r+1;L=projective.target(r);A=projective.U
        pair1=(L,gram.mm(gram.mm(gram.inv(A),L),A))
        pair2=(gram.mm(gram.mm(A,L),gram.inv(A)),L)
        physical={1:projective.lift(pair1),2:projective.lift(pair2)}
        s1=run((0,0,1),t,physical);s2=run((0,0,2),t,physical)
        assert s1==(r*(r*r+2*r+2))**2>0
        assert s2==(r*(r*r-2))**2>0
        # The old independent zero bridges cannot annihilate this rank-one reset.
        assert not reset4.zero(reset4.scale(RESET,s1*s2))
        separation+=1
    return dict(finite_one_relator_accepting_word_cases=accepted,
                same_word_wrong_input_nonzeros=wrong,missing_input_letter_nonzeros=one_input,
                wrong_prefix_order_nonzeros=bad_order,old_independent_bridge_nonzeros=separation,
                universal_alphabet_numerically_instantiated=False)


def verify():
    return dict(status='PASS_GROUP_AFFINE_GUARDED_MORTALITY10',dimension=10,
                varying_letters=1,fixed_alphabet='one letter per original signed generator, plus one constant rank-one reset',
                input_degree=1,input_loader_operations=2,input_loader_M=1,input_loader_A=1,
                input_loader_witnesses=0,input_loader_equations=0,
                control=control_checks(),input=input_checks(),scalars=scalar_checks(),groups=group_checks(),
                scope='Unrestricted mortality for one ordinary-input affine matrix over a fixed alphabet. '
                      'Invalid words have a nonzero scalar by a strict growth bound; they are not mapped to zero. '
                      'The universal finite alphabet remains abstract, and no uniform arithmetic word/history certificate is supplied.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
