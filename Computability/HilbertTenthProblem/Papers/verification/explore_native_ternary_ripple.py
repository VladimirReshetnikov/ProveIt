#!/usr/bin/env python3
"""Exact63 native ternary bounded ripple; no complete machine claim."""
from pathlib import Path
from itertools import product
import json
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_base_three_positive_kernel as kernel

PARAMETERS=['q','FA','FB']
OUTER_NAMES=['Jrep','FD','FE','alpha']
CORE_NAMES=kernel.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}


def schedule(borrow=False):
    end1,end2=('FD','FE') if borrow else ('FE','FD')
    prefix=[
        ('twice_J','+','Jrep','Jrep'),
        ('q_rhs','+','twice_J',1),
        ('seed_lhs','+','FE','Jrep'),
        ('twice_D','+','FD','FD'),
        ('seed_rhs','+','twice_D',1),
        ('pair_lhs','+','FA',end1),
        ('pair_rhs','+','FB',end2),
        ('bound_rhs','+','q','Jrep'),
        ('bound_lhs','+','pair_lhs','alpha'),
        ('pack0','*','q','FE'),
        ('pack1','+','FD','pack0'),
        ('pack2','*','q','pack1'),
        ('pack3','+','FB','pack2'),
        ('pack4','*','q','pack3'),
        ('packed','+','FA','pack4'),
    ]
    mask=[('q2','*','q','q'),('L','*','q2','q2'),
          ('n2','*',3,'L'),('pP','*',3,'packed'),('r_rhs','+','pP',2)]
    equalities=[('q','q_rhs'),('seed_lhs','seed_rhs'),
                ('pair_lhs','pair_rhs'),('bound_lhs','bound_rhs')]+kernel.EQUALITIES
    return prefix+mask+kernel.CORE,equalities


def source_residuals(borrow=False):
    z=SYM
    q,A,B,J,Dw,Ew,alpha=[z[n] for n in PARAMETERS+OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in CORE_NAMES]
    P0=A+q*B+q*q*Dw+q**3*Ew
    scale=3*q**4;U,Y=w*scale,s*scale;Q=U*Y*Y
    D=a*a+6*a+8;aux_u=2*r+1+j*c
    pair_lhs=A+(Dw if borrow else Ew)
    pair_rhs=B+(Ew if borrow else Dw)
    return [q-2*J-1,Ew+J-2*Dw-1,pair_lhs-pair_rhs,
            pair_lhs+alpha-q-J,r-3*P0-2,
            Q*(Q+1)*k*k-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*U*Y,
            a-Y*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-D*c*c-1,(i*c*c)**2-D*(f*f-1),
            D*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),aux_u-c-o*f]


def verify_certificate(borrow=False):
    instructions,equalities=schedule(borrow)
    env=dict(SYM)
    histogram=baseline.run_schedule(instructions,env)
    source=source_residuals(borrow)
    u=2*SYM['r']+1+SYM['j']*SYM['c']
    correction=source[12]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(equalities,source)):
        actual=sp.expand(env[left]-env[right])
        extra=correction if index==13 else sp.Integer(0)
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],
                            source=sp.sstr(sp.expand(p)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(instructions,env)
    assert len(primitive)==63 and counts=={'+':31,'*':32}
    assert len(records)==len(source)==len(equalities)==15
    assert len(OUTER_NAMES+CORE_NAMES)==21
    assert all(row.free_symbols<=set(SYM.values()) for row in source)
    used={x for row in instructions for x in row[2:]}|{x for row in equalities for x in row}
    assert set(SYM)<=used
    return dict(mode='borrow' if borrow else 'increment',arithmetic_status='PASS',
                operations=63,primitive_histogram=counts,histogram=histogram,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=21,equations=15,
                primitive_instructions=primitive,equalities=equalities,residuals=records)


def code(raw):
    result=0;place=1
    while raw:
        result+=(raw&1)*place;raw>>=1;place*=3
    return result


def decode(value,width):
    if value<0:return None
    result=0
    for i in range(width):
        value,digit=divmod(value,3)
        if digit>1:return None
        result+=digit<<i
    return None if value else result


def native(value,width):
    return decode(value-(3**width-1)//2,width) is not None


def central_valuation(r):
    def factorial(n):
        value=0
        while n:
            n//=3;value+=n
        return value
    return factorial(2*r)-2*factorial(r)


def verify_outer(q,A,B,Dw,Ew,J,alpha,borrow=False):
    S=A+(Dw if borrow else Ew)
    assert q==2*J+1 and min(A,B,Dw,Ew,J,alpha)>0
    assert Ew+J==2*Dw+1
    assert S==B+(Ew if borrow else Dw)
    assert S+alpha==q+J
    fields=[A,B,Dw,Ew]
    P=sum(F*q**i for i,F in enumerate(fields));L=q**4;scale=3*L;r=3*P+2
    assert S<=3*J and all(F<3*J for F in fields)
    assert q**3<=P and 2*P<3*(L-1)
    assert r>=83 and 2*r<3*scale and scale<r*r
    assert scale>=243 and scale*scale>r+1 and scale*(scale+1)>2*r+1
    assert 12*r<scale*(scale+1)
    assert P%2==r%2==0
    return P,r


def verify_regression():
    prepower=accepted=enumerated=canonical=boundary=0
    samples=[]
    for q in range(3,32,2):
        J=(q-1)//2
        for borrow in (False,True):
            for A,Dw in product(range(1,3*J),repeat=2):
                Ew=2*Dw+1-J
                B=A+Dw-Ew if borrow else A+Ew-Dw
                S=A+(Dw if borrow else Ew)
                alpha=q+J-S
                if min(Ew,B,alpha)<=0:continue
                verify_outer(q,A,B,Dw,Ew,J,alpha,borrow)
                prepower+=1

    for width in range(1,5):
        q=3**width;J=(q-1)//2
        for borrow in (False,True):
            for A,Dw in product(range(1,3*J),repeat=2):
                enumerated+=1
                Ew=2*Dw+1-J
                B=A+Dw-Ew if borrow else A+Ew-Dw
                S=A+(Dw if borrow else Ew);alpha=q+J-S
                if min(Ew,B,alpha)<=0:continue
                P,r=verify_outer(q,A,B,Dw,Ew,J,alpha,borrow)
                vp=central_valuation(r)
                if vp<4*width+1:continue
                accepted+=1
                assert P<q**4
                assert all(0<F<q and native(F,width) for F in (A,B,Dw,Ew))
                old,new=decode(A-J,width),decode(B-J,width)
                assert new==(old-1 if borrow else old+1)
                assert vp==4*width+1
                if len(samples)<8:samples.append(dict(width=width,borrow=borrow,A=A,B=B,
                                                       FD=Dw,FE=Ew,alpha=alpha,P=P,r=r))

    for width in range(1,9):
        q=3**width;J=(q-1)//2
        for borrow in (False,True):
            inputs=range(1,2**width) if borrow else range(2**width-1)
            for raw in inputs:
                k=0
                while ((raw>>k)&1)==(0 if borrow else 1):k+=1
                d=(3**k-1)//2;e=3**k
                A=J+code(raw);B=J+code(raw-1 if borrow else raw+1)
                Dw,Ew=J+d,J+e
                S=A+(Dw if borrow else Ew);alpha=q+J-S
                P,r=verify_outer(q,A,B,Dw,Ew,J,alpha,borrow)
                assert native(P,4*width) and central_valuation(r)==4*width+1
                assert alpha>=1
                canonical+=1
                boundary+=alpha==1
    return dict(prepower_positive_outer_tuples=prepower,
                complete_native_candidate_pairs=enumerated,
                accepted_complete_candidates=accepted,
                canonical_ripples=canonical,canonical_alpha_one_cases=boundary,
                samples=samples,
                scope='Complete positive outer candidates for widths1..4, direct canonical ripples forwidths1..8, and prepower bounds foroddq3..31. The general proof supplies enormous positive Pell witnesses; no such tuple is instantiated.')


def verify():
    return dict(status='PASS_NATIVE_TERNARY_BOUNDED_RIPPLE_COMPONENT',
                variants=[verify_certificate(False),verify_certificate(True)],
                regression=verify_regression(),
                proof='../1980/EXPLORATION_NATIVE_TERNARY_RIPPLE.md',
                scope='Exact63-operation increment and borrow relations on bounded binary counters represented by ternary Boolean digits plusnative offsets. q,A,B are positive parameters. Complete machine control, variable histories, raw numerical input conversion and halting are not supplied.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for row in result['variants']:print(row['mode'],row['operations'],row['primitive_histogram'],row['equations'])
    print(result['regression'])
