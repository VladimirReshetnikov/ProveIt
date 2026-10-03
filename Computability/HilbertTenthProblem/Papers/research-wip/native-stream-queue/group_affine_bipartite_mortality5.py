#!/usr/bin/env python3
"""Five-dimensional unrestricted mortality by affine rank-two linearization.

The alternating-channel lemma handles singular input letters without a
regular-language guard or a restriction on their number or positions.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import random

import group_weighted_reset_mortality4 as parent

gram=parent.gram
reset4=parent.reset4
projective=parent.projective
free=parent.free
TEMPLATE=((0,0,0,0,1),(0,0,0,0,'t'),(0,0,0,0,1),
          (0,0,0,0,'t'),(1,0,'t',0,0))


def loader(alpha=24,beta=12):
    assert alpha>0 and beta>0
    return [('scaled','*',alpha,'x'),('t','+','scaled',beta+1)]


def column(t):return (1,t,1,t)


def row(t):return (1,0,t,0)


def cross(z,u):
    n=len(z);assert len(u)==n
    return tuple(tuple(0 for _ in range(n))+(z[i],) for i in range(n))+(tuple(u)+(0,),)


def input_letter(t):return cross(column(t),row(t))


def lift(D):return reset4.blocks((D,((1,),)))


def fixed_letter(pair):return lift(parent.fixed_letter(pair))


def core(segments,z,u):
    T=cross(z,u);value=T
    for D in segments:value=gram.mm(T,gram.mm(lift(D),value))
    return value


def parity_formula(segments,z,u):
    odd=even=1
    for j,D in enumerate(segments,1):
        value=gram.dot(u,gram.mv(D,z))
        if j%2:odd*=value
        else:even*=value
    k=len(segments)+1;n=len(z)
    if k%2:
        return cross(tuple(odd*v for v in z),tuple(even*v for v in u))
    return reset4.blocks((reset4.scale(reset4.outer(z,u),even),((odd,),)))


def scalar(word,t,pairs):
    return gram.dot(row(t),gram.mv(parent.word_matrix(word,pairs),column(t)))


def input_checks():
    count=powers=0
    for p in range(12):
        for x in (1,2,17,201):
            source=loader(12*2**(p+1),12*2**p)
            env=gram.execute(source,dict(x=x));t=env['t'];T=input_letter(t)
            assert gram.counts(source)==dict(M=1,A=1,operations=2)
            assert T==tuple(tuple(env[v] if isinstance(v,str) else v for v in r) for r in TEMPLATE)
            assert all(v>=0 for r in T for v in r)
            assert T[0][4]*T[4][0]==1  # Constant nonzero two-by-two minor.
            for rows in combinations(range(5),3):
                for cols in combinations(range(5),3):
                    assert parent.parent.determinant(tuple(tuple(T[i][j] for j in cols) for i in rows))==0
            T2=gram.mm(T,T)
            assert gram.mm(T2,T)==reset4.scale(T,1+t)
            for k in range(1,17):
                expected=reset4.scale(T if k%2 else T2,(1+t)**((k-1)//2))
                assert parent.parent.power(T,k)==expected and not reset4.zero(expected);powers+=1
            # Bilinear rank-one reset is conjugate to the committed4D reset.
            R=reset4.outer(column(t),row(t))
            S=((1,0,0,0),(0,1,0,0),(0,0,t,0),(0,0,0,t))
            assert gram.mm(S,R)==gram.mm(parent.reset(t),S)
            count+=1
    return dict(ordinary_program_input_cases=count,affine_25_entry_template=TEMPLATE,
                literal_source=loader(),loader_M=1,loader_A=1,loader_operations=2,
                input_rank=2,input_determinant=0,input_cube_multiplier='1+t',
                nonzero_input_powers=powers,quadratic_reset_conjugacy_cases=count)


def generic_channel_checks():
    rng=random.Random(510278);cases=zeros=0
    def random_matrix(n):
        M=[list(r) for r in gram.ident(n)]
        for _ in range(8):
            a,b=rng.sample(range(n),2);s=rng.choice((-2,-1,1,2))
            M[a]=[x+s*y for x,y in zip(M[a],M[b])]
        return tuple(map(tuple,M))
    for n in (2,3,4,5):
        for case in range(256):
            t=rng.randrange(2,40);z=(1,t)+(0,)*(n-2);u=(1,)+(0,)*(n-1)
            count=rng.randrange(10)
            segments=[random_matrix(n) for _ in range(count)]
            killer=reset4.blocks((((-t,1),(-1,0)),gram.ident(n-2))) if n>2 else ((-t,1),(-1,0))
            if count>=2 and case%2==0:segments[0]=segments[1]=killer
            actual=core(segments,z,u);expected=parity_formula(segments,z,u)
            assert actual==expected
            values=[gram.dot(u,gram.mv(D,z)) for D in segments]
            assert reset4.zero(actual)==(any(v==0 for v in values[::2]) and any(v==0 for v in values[1::2]))
            exterior_left,exterior_right=lift(random_matrix(n)),lift(random_matrix(n))
            full=gram.mm(exterior_left,gram.mm(actual,exterior_right))
            assert reset4.zero(full)==reset4.zero(actual)
            zeros+=reset4.zero(actual);cases+=1
    return dict(exact_generic_parity_and_exterior_cases=cases,forced_or_incidental_zeros=zeros,
                physical_dimensions=[2,3,4,5],maximum_input_occurrences=10)


def paired_checks():
    U,B,I=projective.U,projective.B,gram.I2
    raw=((U,I),(gram.inv(U),I),(B,I),(gram.inv(B),I),
         (I,U),(I,gram.inv(U)),(I,B),(I,gram.inv(B)),(U,B),(gram.inv(U),gram.inv(B)))
    pairs={i+1:p for i,p in enumerate(raw)};rng=random.Random(520278)
    cases=channels=0
    for case in range(1024):
        t=rng.randrange(2,150)
        word=tuple(rng.randrange(1,11) for _ in range(rng.randrange(18)))
        value=scalar(word,t,pairs);a,b,scale,_,_=parent.profile(word,t,pairs)
        assert value==parent.scalar(word,t,pairs)==-(a+t*scale*b)
        assert (value==0)==(a==b==0)
        M=parent.word_matrix(word,pairs);T=input_letter(t)
        assert core((M,M),column(t),row(t))==reset4.scale(T,value)
        if case<128:
            segments=[parent.word_matrix(tuple(rng.randrange(1,11) for _ in range(rng.randrange(6))),pairs)
                      for _ in range(rng.randrange(9))]
            assert core(segments,column(t),row(t))==parity_formula(segments,column(t),row(t));channels+=1
        cases+=1
    return dict(weighted_paired_scalar_and_three_input_cases=cases,
                additional_actual_alphabet_channel_cases=channels)


def group_checks():
    accept=reject=exterior=separated=0
    for y in range(1,17):
        L,relator=free.shifted_a(y),free.defining_relator(y)
        left=free.multiply(free.inverse(free.A),L,free.A)
        by=free.multiply(free.inverse(free.A),free.inverse(L))
        witness=free.pair_witness(left,((by,0,-1),),2)
        assert reset4.fibre_pair(witness,(relator,))==(L,L)
        tokens=sorted(set(witness));ids={token:i+1 for i,token in enumerate(tokens)}
        pairs={ids[token]:reset4.pair_matrices(reset4.fibre_pair((token,),(relator,))) for token in tokens}
        word=tuple(ids[token] for token in reversed(witness));t=12*y+1
        M=parent.word_matrix(word,pairs);value=core((M,M),column(t),row(t))
        assert scalar(word,t,pairs)==0 and reset4.zero(value);accept+=1
        assert scalar(word,t+12,pairs)!=0 and not reset4.zero(core((M,M),column(t+12),row(t+12)));reject+=1
        E=fixed_letter(next(iter(pairs.values())))
        assert reset4.zero(gram.mm(E,gram.mm(value,E)));exterior+=1
        # Exactly two input occurrences can never be zero, even with an accepting bridge.
        assert not reset4.zero(core((M,),column(t),row(t)))
    for y in range(1,33):
        t=12*y+1;L=projective.target(12*y);A=projective.U
        pairs={1:(L,gram.mm(gram.mm(gram.inv(A),L),A)),
               2:(gram.mm(gram.mm(A,L),gram.inv(A)),L)}
        matrices=[parent.fixed_letter(pairs[i]) for i in (1,2,1,2,1,2)]
        assert scalar((1,),t,pairs) and scalar((2,),t,pairs)
        assert not reset4.zero(core(matrices,column(t),row(t)));separated+=1
    return dict(finite_one_relator_three_input_zeros=accept,wrong_input_nonzeros=reject,
                nonempty_exterior_zero_cases=exterior,two_input_nonzero_with_zero_bridge=accept,
                independent_one_block_bridges_nonzero=separated,
                numerical_universal_alphabet_instantiated=False)


def verify():
    return dict(status='PASS_GROUP_AFFINE_BIPARTITE_MORTALITY5',dimension=5,
                input_degree=1,input_loader_operations=2,varying_letters=1,
                fixed_alphabet='one lifted scaled matrix per original signed paired generator',
                input=input_checks(),generic_channels=generic_channel_checks(),
                paired=paired_checks(),groups=group_checks(),
                scope='The rank-two varying input letter is singular, but exact parity-channel '
                      'factorization proves unrestricted mortality iff one full paired endpoint '
                      'exists. No free regular-language constraint, numerical75/88 improvement, '
                      'or arbitrary supplied-word Diophantine certificate is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
