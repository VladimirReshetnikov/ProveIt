#!/usr/bin/env python3
"""Nine-dimensional mortality, paid selected-duration traces, and uniform projection."""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import factorial
from pathlib import Path
import random

import group_affine_guarded_mortality10 as parent

gram=parent.gram
projective=parent.projective
reset4=parent.reset4
CT=((1,0,0),(0,1,0),(1,1,1))
CF=((1,0,0),(3,1,0),(0,0,1))
START=parent.PHYSICAL_START+(1,0,-2)
ROW=projective.ROW+(0,0,4)
RESET=reset4.outer(START,ROW)


def input_letter(t):
    return reset4.blocks((parent.physical_input(t),parent.scale01(CT,t)))


def fixed_letter(a):
    coefficient=parent.weighted_bound(a)
    return reset4.blocks((a,reset4.scale(CF,coefficient)))


def run(word,t,physical):
    vector=START
    for token in word:
        vector=gram.mv(input_letter(t) if token==0 else fixed_letter(physical[token]),vector)
    return gram.dot(ROW,vector)


def control_checks():
    count=0
    for length in range(11):
      for word in product((0,1),repeat=length):
        state=(1,0,-2)
        for token in word:state=gram.mv(CT if token==0 else CF,state)
        n=word.count(0);f=len(word)-n
        I=sum(word[i] and word[j]==0 for i in range(length) for j in range(i+1,length))
        assert state==(1,3*f,n-2+3*I)
        assert (state[2]==0)==(len(word)>=2 and word[:2]==(0,0) and all(word[2:]))
        count+=1
    def guard(word):
        return word.count(0)-2+3*sum(word[i] and word[j]==0
            for i in range(len(word)) for j in range(i+1,len(word)))
    prefixes=((),(1,),(0,));suffixes=((),(0,),(1,0))
    H=tuple(tuple(guard(a+b) for b in suffixes) for a in prefixes)
    a,b,c=H
    determinant=a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
    assert determinant==-9
    return dict(exhaustive_control_words=count,Hankel_minor=H,Hankel_determinant=determinant,
                scope='Rank three is minimal for this exact scalar series over Q, not for all possible guards.')


def mortality_checks():
    rng=random.Random(920262);count=dense=0
    A=((1,1),(0,1));B=((1,0),(1,1));I=gram.I2
    pairs=((A,I),(gram.inv(A),I),(B,I),(gram.inv(B),I),(I,A),(I,gram.inv(A)),(I,B),(I,gram.inv(B)))
    physical={i+1:projective.lift(pair) for i,pair in enumerate(pairs)}
    assert gram.dot(ROW,START)==-6 and gram.mm(RESET,RESET)==reset4.scale(RESET,-6)
    template=input_letter('input_t')
    assert len(template)==9 and {v for row in template for v in row}=={0,1,'input_t'}
    for case in range(768):
        t=rng.randrange(3,60)
        word=tuple(rng.randrange(9) for _ in range(rng.randrange(12)))
        if case%4==0:word=(0,0)+tuple(rng.randrange(1,9) for _ in range(rng.randrange(8)))
        _,guard,growth,scalar=parent.direct_profile(word,t,physical)
        actual=run(word,t,physical)
        assert actual==parent.run(word,t,physical)==scalar+4*growth*guard
        if guard:assert actual!=0
        if case<64:
            M=gram.ident(9)
            for token in word:M=gram.mm(input_letter(t) if token==0 else fixed_letter(physical[token]),M)
            assert gram.mm(gram.mm(RESET,M),RESET)==reset4.scale(RESET,actual)
            dense+=1
        count+=1
    return dict(exact_scalar_agreements_with_10D=count,dense_reset_factorizations=dense,
                input_matrix_template=template,loader=parent.loader(),
                input_loader_counts=gram.counts(parent.loader()),input_determinant='t^3*(t^2-1)^2')


def interpolate(values):
    """Integer coefficients of s! times interpolation at nodes1,...,s."""
    s=len(values);D=factorial(s);result=[Fraction(0) for _ in range(s)]
    for j,value in enumerate(values,1):
        polynomial=[1];denominator=1
        for k in range(1,s+1):
            if k==j:continue
            new=[0]*(len(polynomial)+1)
            for i,c in enumerate(polynomial):new[i]-=k*c;new[i+1]+=c
            polynomial=new;denominator*=j-k
        for i,c in enumerate(polynomial):result[i]+=Fraction(D*value*c,denominator)
    assert all(c.denominator==1 for c in result)
    return tuple(int(c) for c in result)


def build_duration(table,n,alpha=24,beta=12):
    """Choose exactly n fixed paired matrices; table and n are compiler data."""
    table=tuple(table);s=len(table);assert s>=2 and n>=1 and alpha>0 and beta>0
    columns=tuple(tuple(value for matrix in pair for row in matrix for value in row) for pair in table)
    assert all(len(column)==8 for column in columns)
    for pair in table:
        assert all(a[0][0]*a[1][1]-a[0][1]*a[1][0]==1 for a in pair)
    coefficients=tuple(interpolate([column[i] for column in columns]) for i in range(8))
    D=factorial(s);source=list(parent.loader(alpha,beta));comparisons=[]
    auxiliaries=['height'] if n>=2 else []
    if n>=2:source.append(('height_scaled','*',D,'height'))
    for step in range(n):
        branch=f'branch{step}';slack=f'branch_bound{step}'
        auxiliaries += [branch,slack]
        bound=f'branch_sum{step}';source.append((bound,'+',branch,slack));comparisons.append((bound,s+1))
        rows=(0,2) if step==n-1 else (0,1,2,3)
        needed=tuple(k for row in rows for k in (2*row,2*row+1))
        lookup={}
        for column in needed:
            running=coefficients[column][-1]
            for level in range(s-2,-1,-1):
                mul=f'lookup_{step}_{column}_{level}_mul';add=f'lookup_{step}_{column}_{level}'
                source += [(mul,'*',running,branch),(add,'+',mul,coefficients[column][level])]
                running=add
            lookup[column]=running
        if step:
            for row in range(4):source.append((f'raw_{step}_{row}','-',f'state_{step}_{row}','height'))
        for row in rows:
            left,right=lookup[2*row],lookup[2*row+1]
            output=f'action_{step}_{row}'
            if step==0:
                mul=f'action_{step}_{row}_mul'
                source += [(mul,'*',right,'input_t'),(output,'-',mul,left)]
            else:
                block=2*(row//2);a=f'action_{step}_{row}_left';b=f'action_{step}_{row}_right'
                source += [(a,'*',left,f'raw_{step}_{block}'),
                           (b,'*',right,f'raw_{step}_{block+1}'),(output,'+',a,b)]
            if step==n-1:comparisons.append((output,0))
            else:
                witness=f'state_{step+1}_{row}';auxiliaries.append(witness)
                scaled=f'state_scaled_{step+1}_{row}';shifted=f'action_shifted_{step}_{row}'
                source += [(scaled,'*',D,witness),(shifted,'+',output,'height_scaled')]
                comparisons.append((scaled,shifted))
    counts=gram.counts(source)
    expected=((8*s-1,2,3) if n==1 else ((16*n-8)*s+9*n-11,6*n-3,5*n-2))
    assert (len(source),len(auxiliaries),len(comparisons))==expected
    M=4*s-1 if n==1 else (8*n-4)*s+4*n-6
    AA=4*s if n==1 else (8*n-4)*s+5*n-5
    assert counts==dict(M=M,A=AA,operations=M+AA)
    return dict(s=s,n=n,alpha=alpha,beta=beta,denominator=D,table=table,coefficients=coefficients,
                parameters=['x'],auxiliaries=auxiliaries,source=source,comparisons=comparisons,
                positive_witnesses=len(auxiliaries),equations=len(comparisons),**counts)


def polynomial_source(packet):
    source=list(packet['source']);squares=[]
    for i,(a,b) in enumerate(packet['comparisons']):
        difference=f'residual{i}';square=f'square{i}'
        if b==0:difference=a
        else:source.append((difference,'-',a,b))
        source.append((square,'*',difference,difference));squares.append(square)
    running=squares[0]
    for i,square in enumerate(squares[1:],1):
        new=f'sum{i}';source.append((new,'+',running,square));running=new
    return source,running


def manual(packet,z):
    s,n,D=packet['s'],packet['n'],packet['denominator'];rr=[]
    t=packet['alpha']*z['x']+packet['beta']+1
    for step in range(n):
        branch=z[f'branch{step}'];rr.append(branch+z[f'branch_bound{step}']-s-1)
        coeff=[sum(c*branch**i for i,c in enumerate(poly)) for poly in packet['coefficients']]
        raw=(-1,t,-1,t) if step==0 else tuple(z[f'state_{step}_{row}']-z['height'] for row in range(4))
        for row in ((0,2) if step==n-1 else range(4)):
            block=2*(row//2);value=coeff[2*row]*raw[block]+coeff[2*row+1]*raw[block+1]
            rr.append(value if step==n-1 else D*z[f'state_{step+1}_{row}']-value-D*z['height'])
    return rr


def fixture(packet,word,x):
    assert len(word)==packet['n']
    t=packet['alpha']*x+packet['beta']+1;state=(-1,t,-1,t);states=[]
    z={'x':x}
    for step,branch in enumerate(word):
        assert 1<=branch<=packet['s']
        z[f'branch{step}']=branch;z[f'branch_bound{step}']=packet['s']+1-branch
        pair=packet['table'][branch-1]
        state=gram.mv(pair[0],state[:2])+gram.mv(pair[1],state[2:]);states.append(state)
    if packet['n']>=2:
        z['height']=1+max(abs(v) for state in states[:-1] for v in state)
        for step,state in enumerate(states[:-1],1):
            z.update({f'state_{step}_{row}':v+z['height'] for row,v in enumerate(state)})
    return z,states[-1]


def duration_checks():
    rng=random.Random(951824);records=[];raw_cases=traces=accepts=mutations=0
    I=gram.I2;A=projective.U;B=projective.B
    pool=((I,I),(A,I),(gram.inv(A),B),(B,A),(gram.inv(B),gram.inv(A)))
    example=None
    for s in range(2,6):
      table=pool[:s]
      for n in range(1,6):
        packet=build_duration(table,n);source,out=polynomial_source(packet)
        expected=8*s+5 if n==1 else (16*n-8)*s+24*n-20
        assert sum(b==0 for _,b in packet['comparisons'])==2
        assert len(source)==expected==packet['operations']+3*packet['equations']-3
        degrees={name:1 for name in packet['parameters']+packet['auxiliaries']}
        def degree(v):return degrees[v] if isinstance(v,str) else 0
        for name,op,a,b in source:degrees[name]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
        assert degrees[out]<=2*s
        for branch in range(1,s+1):
            entries=tuple(value for matrix in table[branch-1] for row in matrix for value in row)
            assert tuple(sum(c*branch**i for i,c in enumerate(poly)) for poly in packet['coefficients'])==tuple(packet['denominator']*v for v in entries)
        for case in range(32):
            z={key:rng.randrange(1,8) if case<24 else rng.randrange(-4,5)
               for key in packet['parameters']+packet['auxiliaries']}
            env=gram.execute(source,z);rr=manual(packet,z)
            assert [env[a]-(env[b] if isinstance(b,str) else b) for a,b in packet['comparisons']]==rr
            assert env[out]==sum(r*r for r in rr);raw_cases+=1
            word=tuple(rng.randrange(1,s+1) for _ in range(n));z,last=fixture(packet,word,rng.randrange(1,8))
            assert min(z.values())>0
            assert gram.execute(source,z)[out]==packet['denominator']**2*(last[0]**2+last[2]**2)
            traces+=1
        records.append(dict(s=s,n=n,certificate=packet['operations'],M=packet['M'],A=packet['A'],
                            positive_witnesses=packet['positive_witnesses'],equations=packet['equations'],
                            polynomial_operations=len(source),polynomial_degree_upper_bound=2*s))
        if s==2 and n==2:example=packet
    L=projective.target(36);table=((I,I),(L,L))
    for n in range(1,9):
        packet=build_duration(table,n);source,out=polynomial_source(packet)
        z,last=fixture(packet,(1,)*(n-1)+(2,),1)
        assert last==(0,1,0,1) and gram.execute(source,z)[out]==0;accepts+=1
        for mutation in ('input','slack','branch'):
            bad=dict(z)
            if mutation=='input':bad['x']+=1
            elif mutation=='slack':bad['branch_bound0']+=1
            else:bad['branch0']=3
            assert gram.execute(source,bad)[out]>0;mutations+=1
        if n>=2:
            bad=dict(z);bad['state_1_0']+=1
            assert gram.execute(source,bad)[out]>0;mutations+=1
    return dict(records=records,source_example=example,arbitrary_full_residual_SOS_cases=raw_cases,
                independent_selected_traces=traces,accepted_exact_traces=accepts,
                rejected_input_selector_slack_state_mutations=mutations)


def uniform_checks():
    import group_range_projective_compiler as generic
    import group_projective_shifted_boundary as boundary
    import group_projective_factored_native_index as compact
    records=[]
    for codes in (((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
        old=generic.build(codes)
        oldpoly,_=generic.shared.polynomial_source(old)
        assert len(oldpoly)==old['operations']+77
        reflected=boundary.reflect_codes(codes)
        for code,changed in zip(codes,reflected):
            assert tuple(boundary.physical.inverse_letter(letter) for letter in code)==changed
        packet=compact.build(reflected,controller_mask=True,compute_length=True)
        poly,_=compact.polynomial_source(packet)
        m=packet['m'];h=packet['h'];port=packet['projection_additions'];flow=packet['flow']['operations']
        C=3*m+3*h+port+185+flow-3*min(h,3)-1
        assert packet['operations']==C-1 and len(poly)==C+25
        assert packet['equations']==9 and packet['positive_witnesses']==m+27
        records.append(dict(original_codes=codes,reflected_codes=reflected,m=m,
                            generic_certificate=old['operations'],generic_polynomial=len(oldpoly),
                            compact_certificate=packet['operations'],compact_polynomial=len(poly),
                            compact_equations=9,compact_positive_witnesses=m+27,
                            compact_degree=110*m+616))
    return dict(records=records,scope='Literal imports of named paid sources. The mortality-to-endpoint equivalence uses Gamma, or its stated modulo-four subgroup, and compatible t=1 mod4. Compact import additionally uses the stated fixed margin and reflected alphabet.')


def verify():
    return dict(status='PASS_GROUP_AFFINE_GUARDED_MORTALITY9',dimension=9,
                control=control_checks(),mortality=mortality_checks(),selected_duration=duration_checks(),
                uniform_projection=uniform_checks(),
                scope='A complete existential mortality predicate transfers to the existing paid paired-vector compiler. This does not verify an arbitrary supplied mortality word, and no new numerical universal alphabet or lower75/88 bound is asserted.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
