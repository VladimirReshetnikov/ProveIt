#!/usr/bin/env python3
"""Six-dimensional affine-input mortality with an invertible cone guard.

Fixed program data and the inherited universal alphabet are distinguished
from finite one-relator examples. No arbitrary-word Diophantine shortcut
is inferred from the two-operation matrix loader.
"""
import argparse
import json
from pathlib import Path
import random

import group_affine_weighted_mortality7 as parent

gram=parent.gram
projective=parent.projective
reset4=parent.reset4
free=parent.free
CT=((1,1),(0,1))
CF=((1,0),(2,1))
CONTROL_START=(-2,1)
CONTROL_ROW=(1,0)
START=parent.START4+CONTROL_START
ROW=parent.ROW4+(4,0)
RESET=reset4.outer(START,ROW)


def loader(alpha=24,beta=12):
    assert alpha>0 and beta>0
    return [('scaled','*',alpha,'x'),('input_t','+','scaled',beta+1)]


def input_letter(t):
    control=tuple(tuple(t if v else 0 for v in row) for row in CT)
    return reset4.blocks((parent.physical_input(t),control))


def fixed_letter(pair):
    physical,_,mu=parent.fixed_data(pair)
    return reset4.blocks((physical,reset4.scale(CF,mu)))


def run(word,t,pairs):
    value=START
    for token in word:
        value=gram.mv(input_letter(t) if token==0 else fixed_letter(pairs[token]),value)
    return gram.dot(ROW,value)


def control_state(word):
    value=CONTROL_START
    for token in word:value=gram.mv(CT if token==0 else CF,value)
    return value


def control_checks():
    # Independent finite recognizer:0 beforeT,1 oneT,2 TTF*,3 negative,4 positive.
    transitions={0:(1,3),1:(2,3),2:(4,2),3:(3,3),4:(4,4)}
    frontier=[((),CONTROL_START,0)];count=valid=negative=positive=0
    for length in range(16):
        following=[]
        for word,value,state in frontier:
            assert (value[0]==0)==(state==2)
            assert (state==2)==(len(word)>=2 and word[:2]==(0,0) and all(word[2:]))
            if state==0:assert value==(-2,1)
            elif state==1:assert value==(-1,1)
            elif state==2:assert value==(0,1);valid+=1
            elif state==3:assert max(value)<0;negative+=1
            else:assert min(value)>0;positive+=1
            count+=1
            if length<15:
                for token,matrix in ((0,CT),(1,CF)):
                    following.append((word+(token,),gram.mv(matrix,value),transitions[state][token]))
        frontier=following
    prefixes=((),(0,));suffixes=((),(0,))
    hankel=tuple(tuple(control_state(a+b)[0] for b in suffixes) for a in prefixes)
    assert hankel==((-2,-1),(-1,0)) and parent.determinant(hankel)==-1
    assert control_state((1,0))[0]==-5
    old=parent.parent.gram.mv(parent.parent.CT,parent.parent.gram.mv(parent.parent.CF,(1,0,-2)))
    assert old[2]==2  # Same zero language, different scalar series.
    return dict(exhaustive_binary_control_words=count,valid_words=valid,
                negative_cone_words=negative,positive_cone_words=positive,
                exact_rank_two_minor=hankel,minor_determinant=-1,
                changed_series_example=dict(word=['F','T'],new_scalar=-5,old_scalar=2))


def input_checks():
    template=input_letter('input_t')
    assert len(template)==6 and {v for row in template for v in row}=={-1,0,1,'input_t'}
    assert parent.determinant(CT)==parent.determinant(CF)==1
    assert gram.dot(ROW,START)==-6 and gram.mm(RESET,RESET)==reset4.scale(RESET,-6)
    count=0
    for p in range(12):
        for x in (1,2,17,201):
            alpha,beta=12*2**(p+1),12*2**p
            source=loader(alpha,beta);t=gram.execute(source,dict(x=x))['input_t']
            assert gram.counts(source)==dict(M=1,A=1,operations=2)
            assert input_letter(t)==tuple(tuple(t if isinstance(v,str) else v for v in row)
                                         for row in template)
            assert parent.determinant(input_letter(t))==t**3
            assert run((0,0),t,{})==-(t+1)
            count+=1
    return dict(ordinary_input_cases=count,affine_36_entry_template=template,
                loader=loader(),loader_M=1,loader_A=1,loader_operations=2,
                input_determinant='t^3',reset_square_multiplier=-6)


def scalar_checks():
    U,B=projective.U,projective.B;I=gram.I2
    raw=((U,I),(gram.inv(U),I),(B,I),(gram.inv(B),I),
         (I,U),(I,gram.inv(U)),(I,B),(I,gram.inv(B)))
    pairs={i+1:pair for i,pair in enumerate(raw)}
    rng=random.Random(620273);valid=invalid=negative=dense=reset_pairs=0
    def product_matrix(word,t):
        value=gram.ident(6)
        for token in word:
            matrix=input_letter(t) if token==0 else fixed_letter(pairs[token])
            value=gram.mm(matrix,value)
        return value
    for case in range(1536):
        t=rng.randrange(3,90)
        word=tuple(rng.randrange(9) for _ in range(rng.randrange(20)))
        if case%4==0:word=(0,0)+tuple(rng.randrange(1,9) for _ in range(rng.randrange(12)))
        physical,rho,_,Lambda,paired=parent.direct_profile(word,t,pairs)
        control=control_state(word);guard=control[0];actual=run(word,t,pairs)
        assert actual==physical+4*rho*guard
        assert (actual==0)==(parent.run(word,t,pairs)==0)
        if guard:
            assert actual!=0 and (actual>0)==(guard>0);invalid+=1;negative+=guard<0
        else:
            assert word[:2]==(0,0) and all(word[2:])
            a,b=(gram.mv(M,(-1,t))[0] for M in paired)
            assert abs(a)<t*Lambda and physical==a+t*Lambda*b
            assert (actual==0)==(a==b==0);valid+=1
        if case<96:
            M=product_matrix(word,t)
            assert gram.dot(ROW,gram.mv(M,START))==actual
            assert gram.mm(gram.mm(RESET,M),RESET)==reset4.scale(RESET,actual);dense+=1
        if case<64:
            other=tuple(rng.randrange(9) for _ in range(rng.randrange(8)))
            M,N=product_matrix(word,t),product_matrix(other,t)
            value=gram.mm(gram.mm(gram.mm(gram.mm(RESET,N),RESET),M),RESET)
            assert value==reset4.scale(RESET,actual*run(other,t,pairs));reset_pairs+=1
    return dict(exact_arbitrary_word_scalar_cases=1536,valid_prefix_cases=valid,
                invalid_word_nonzeros=invalid,negative_guard_cases=negative,
                dense_two_reset_factorizations=dense,dense_three_reset_factorizations=reset_pairs,
                zero_equivalence_to_7D_cases=1536)


def group_checks():
    accepted=wrong=bad=missing=separated=0
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
        assert run((suffix[0],0,0)+suffix[1:],t,pairs)!=0;bad+=1
        assert run((0,)+suffix,t,pairs)!=0;missing+=1
    for y in range(1,25):
        r=12*y;t=r+1;L=projective.target(r);A=projective.U
        pairs={1:(L,gram.mm(gram.mm(gram.inv(A),L),A)),
               2:(gram.mm(gram.mm(A,L),gram.inv(A)),L)}
        a=run((0,0,1),t,pairs);b=run((0,0,2),t,pairs)
        assert a and b and not reset4.zero(reset4.scale(RESET,a*b));separated+=1
    rotation=((0,-1),(1,0));minusI=((-1,0),(0,-1))
    assert run((0,0,1),13,{1:(rotation,minusI)})==0
    return dict(finite_one_relator_accepting_words=accepted,wrong_input_nonzeros=wrong,
                wrong_order_nonzeros=bad,missing_input_nonzeros=missing,
                independent_bridge_nonzeros=separated,
                omitted_subgroup_hypothesis_counterexample_retained=True,
                universal_numerical_alphabet_instantiated=False)


def verify():
    return dict(status='PASS_GROUP_AFFINE_CONE_MORTALITY6',dimension=6,
                input_degree=1,input_loader_operations=2,varying_letters=1,
                fixed_alphabet='one per original signed paired letter, plus one constant rank-one reset',
                guard=control_checks(),inherited_power_bounds=parent.power_checks(),input=input_checks(),
                scalars=scalar_checks(),groups=group_checks(),
                scope='A different two-dimensional guard has exactly the zero language TTF*. '
                      'Full unrestricted mortality inherits the universal paired endpoint. '
                      'No global mortality-dimension lower bound, new numerical75/88 result, '
                      'or arbitrary supplied-word Diophantine certificate is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
