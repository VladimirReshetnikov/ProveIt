#!/usr/bin/env python3
"""Standalone105: doubled raw coordinates over the positive-Z106 source."""
from pathlib import Path
import json
import sympy as sp
import explore_factored_raw_blocks as old
from explore_native_ternary_ripple import native,central_valuation

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=old.OUTER_NAMES
SYM=old.SYM
FIELDS=old.FIELDS
DOUBLED=['Jrep','H','T','A0','A1','Kp','Km','Z','Dzero','PC','PV']


def build():
    previous,pairs,source,origins=old.build();ops=[]
    for name,op,left,right in previous:
        if name=='twice_raw_packed':continue
        if name=='q_rhs':left='Jrep'
        if name=='input':op,left,right='*',4,'x'
        if name=='packed_index_rhs':right='raw_packed'
        ops.append((name,op,left,right))
    source=list(source)
    source[origins.index(0)]=SYM['q']-SYM['Jrep']-1
    source[origins.index(7)]+=2*SYM['x']
    source[origins.index(8)]+=2*SYM['x']
    raw=sum(old.old.SYM[name]*SYM['q']**i for i,name in enumerate(FIELDS)).subs(old.SUB,simultaneous=True)
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-SYM['q']**12-raw)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==105 and counts=={'+':49,'*':56}
    assert len(source)==len(pairs)==22 and len(OUTER_NAMES+CORE_NAMES)==34
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if origin==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,(i,origin)
        records.append(dict(index=i,old_index=origin,equality=[left,right],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    # The inverse map is rational until the independent decoding proof has
    # shown all eleven coordinates even. The old input slack is alpha+2x.
    sub={SYM[n]:SYM[n]/2 for n in DOUBLED}
    sub[SYM['alphaI']]=SYM['alphaI']+2*SYM['x']
    prior=old.build()[2];factors=[]
    unchanged={0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,24}
    for i,origin in enumerate(origins):
        factor=1 if origin in unchanged else 2
        assert sp.expand(source[i]-factor*prior[i].subs(sub,simultaneous=True))==0,(i,origin)
        factors.append(dict(index=i,old_index=origin,factor=factor))
    assert ZALL>PROGRAM['g']*PROGRAM['S']>=PROGRAM['g']*PROGRAM['I']
    assert PROGRAM['K']>=3 and PROGRAM['zeros'][0]==0 and PROGRAM['signs'][0]==1
    return dict(status='PASS',operations=105,primitive_histogram=counts,unknown_count=34,equations=22,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                inverse_source_factors=factors,doubled_coordinates=DOUBLED,
                scope='All105 primitives and22 fresh source polynomials, including the exact divided-coordinate source transport. Integrality of the inverse is established by the separate general decoding proof.')


def boolean(v):
    if v<0:return False
    while v:
        v,d=divmod(v,3)
        if d>1:return False
    return True


def words(n):
    out=[0];p=1
    for _ in range(n):out += [v+p for v in out];p*=3
    return sorted(out)


def verify_geometry_and_initial_carries():
    geometry=aligned=pair_cases=carry_cases=parity_cases=0
    for m in range(1,9):
        R=3**m
        for e in range(1,49):
            q=3**e
            if 2*(q-1)%(R-1)==0:
                assert e%m==0
                H=2*(q-1)//(R-1);assert H%2==0
                aligned+=1
            geometry+=1
    for m in range(2,8):
        R=3**m;h=(R//3-1)//2;ws=words(m)
        for a in ws:
            for b in ws:
                if (a-b-h-1)%R==0:
                    assert a==R//3 and b==h
                    carry_cases+=1
                pair_cases+=1
        normals=[2*a for a in ws if a<=h]
        bad=2*R//3-1
        for a in normals:
            assert a%2==0 and a<=R//3-1
            assert (a+bad)%R%2==1
            parity_cases+=1
        assert (bad+bad)%R==R//3-2 and (bad+bad)%R%2==1
        parity_cases+=1
    # The need for the new proof is real: isolated doubled guards can carry.
    q=729;J=q-1;T=J-2;A=5
    low=(A+T)%q;high=A+(A+T)//q
    assert low==2 and high==6 and boolean(low//2) and boolean(high//2) and A%2==1
    return dict(exponent_geometry_cases=geometry,admissible_aligned_cases=aligned,
                initial_boolean_pair_cases=pair_cases,unique_overflow_pairs=carry_cases,
                initial_parity_exclusions=parity_cases,
                isolated_guard_alias=dict(q=q,T=T,A=A,actual_chunks=[low,high]),
                scope='Exact geometry and initial-block carry lemmas; the isolated alias deliberately shows why individual range bounds alone do not prove even raw tracks.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;R=c['Rmin'];W=R**3;q=R**blocks;j=(q-1)//2;h=(q-1)//(R-1)
    values=[2*x,0,0];a0=a1=kp=km=z0=0
    aligned=old.old.old.ALIGNED
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        value=values[lane];assert 0<=value<R//3
        if c['zeros'][state]:assert value==0
        aa,bb=aligned.single.split_ternary(value,b);weight=R**b
        a0+=aa*weight;a1+=bb*weight
        if c['signs'][state]==1:kp+=weight
        else:km+=weight
        z0+=c['zeros'][state]*weight;values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0]
    d=h-z0;t=j-((R-3)//6)*d
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*kp-c['hz']*d
    tc=C+j-c['S']*h;tv=V+ZALL*h
    original=[kp,a0+t,a0,a1+t,a1,km,z0,d,C,V,tc,tv]
    fields=[2*v for v in original]
    raw=sum(v*q**i for i,v in enumerate(fields));L=q**12
    assert raw%2==0 and L%2==1
    r=(L+raw-1)//2
    vals=dict(x=x,q=q,Jrep=2*j,W=W,H=2*h,v=q//W,R=R,T=2*t,A0=2*a0,A1=2*a1,
              Kp=2*kp,Km=2*km,Z=2*z0,Dzero=2*d,alphaI=R-4*x,PC=2*C,PV=2*V,r=r,beta=L-r)
    assert min(vals.values())>0 and all(v%2==0 for v in fields)
    ops,pairs,source,origins=build();sub={SYM[n]:v for n,v in vals.items()}
    indices=[i for i,o in enumerate(origins) if o<10 or o>=20]
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(boolean(v//2) and v<q for v in fields)
    assert native(r,12*ell) and r%3==2 and r%2==0 and q**11<r<L<r*r
    assert r==sum((j+v)*q**i for i,v in enumerate(original))
    valuation=central_valuation(r);assert valuation==12*ell
    return dict(x=x,serial_blocks=blocks,counter_width=c['B'],outer_residuals=len(indices),
                doubled_conceptual_fields=12,all_retained_doubled_coordinates_even=True,
                input_bound='4*x+alphaI=R',packed_index_unchanged_from_106=True,
                packed_bits=r.bit_length(),valuation=valuation,
                scope='Fresh full doubled outer tuple and exact valuation; the old packed index is unchanged at these sufficiently wide canonical frames. Full positive Pell tuples follow from the proved converse.')


def verify():
    return dict(status='PASS_DOUBLED_RAW_COORDINATES_105',arithmetic=verify_certificate(),
                geometry_and_carries=verify_geometry_and_initial_carries(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_DOUBLED_RAW_COORDINATES.md',
                scope='Standalone105 over106 with positive Z retained, full independent proof/source reviews and fresh verification. No composition with either eliminated Z or complemented guards is asserted. Existing universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['geometry_and_carries']);print(result['canonical'])
