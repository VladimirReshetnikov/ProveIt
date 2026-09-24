#!/usr/bin/env python3
"""General-scale43 Pell kernels of both signs and sharp unit-two mask."""
from pathlib import Path
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
from round37_1980_base_two_pell_regression import pell_power
import explore_base_three_positive_kernel as previous

PARAMETERS=['D0','r']
AUXILIARIES=[name for name in previous.CORE_NAMES if name!='r']
SYM={name:sp.Symbol(name) for name in PARAMETERS+AUXILIARIES}
EQUALITIES=previous.EQUALITIES[1:]


def schedule(sign=1):
    assert sign in (-1,1)
    result=[]
    for row in previous.CORE:
        row=tuple('D0' if value=='n2' else value for value in row)
        if sign==-1 and row[0]=='aux_u_rhs':row=('aux_u_rhs','-','of','c')
        if sign==-1 and row[0]=='H17':row=('H17','-','jc','tr1')
        result.append(row)
    return result


def source_residuals(sign=1):
    z=SYM
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[name] for name in previous.CORE_NAMES]
    U,Y=w*z['D0'],s*z['D0'];Q=U*Y*Y;D=a*a+6*a+8
    u=j*c+sign*(2*r+1)
    return [Q*(Q+1)*k*k-tau*(tau+1),c-Y*k-eta,k-eta-zeta,
            k-r-1-h*U*Y,a-Y*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-D*c*c-1,(i*c*c)**2-D*(f*f-1),
            D*(f*f-1)*(u*u-y*y)-(1-y*y),u-o*f-sign*c]


def verify_certificate(sign=1):
    instructions=schedule(sign);env=dict(SYM)
    histogram=baseline.run_schedule(instructions,env)
    source=source_residuals(sign)
    u=SYM['j']*SYM['c']+sign*(2*SYM['r']+1)
    correction=source[7]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=correction if index==8 else sp.Integer(0)
        assert sp.expand(actual-residual-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitives,counts=verify_primitives(instructions,env)
    assert len(primitives)==43 and counts=={'+':18,'*':25}
    assert len(records)==len(source)==len(EQUALITIES)==10
    assert len(AUXILIARIES)==16 and all(p.free_symbols<=set(SYM.values()) for p in source)
    used={x for row in instructions for x in row[2:]}|{x for pair in EQUALITIES for x in pair}
    assert set(SYM)<=used
    return dict(sign=sign,arithmetic_status='PASS',operations=43,primitive_histogram=counts,
                histogram=histogram,parameters=PARAMETERS,positive_auxiliaries=AUXILIARIES,
                auxiliary_count=16,equations=10,primitive_instructions=primitives,
                equalities=EQUALITIES,residuals=records,
                preliminary_hypotheses='D0>=81,r>=27,r<2D0,D0<r^2',
                converse_hypotheses='D0 is a power of3 and divides binom(2r,r); sign=(-1)^r')


def vfact(n):
    result=0
    while n:n//=3;result+=n
    return result


def valuation(n):return vfact(2*n)-2*vfact(n)


def mask_expected(n,N):
    if n%3!=2:return False
    for _ in range(N):
        n,digit=divmod(n,3)
        if digit not in (1,2):return False
    return n==0


def check_mask():
    cases=overflow=0;endpoints=[]
    for N in range(1,11):
        L=3**N;star=(3*L-1)//2
        for packed in range(star+1):
            val=valuation(packed)
            assert (val>=N)==(packed<L and mask_expected(packed,N))
            if packed>=L:
                assert val<N;overflow+=1
            cases+=1
        assert valuation(star)==0
        assert valuation(star+1)==N+1
        assert valuation(star+2)==N
        endpoints.append(dict(N=N,L=L,last_rejected=star,
                              first_false_acceptance=star+1,first_false_valuation=N+1,
                              opposite_parity_false_acceptance=star+2,second_false_valuation=N))
    return dict(complete_cases=cases,rejected_overflow_cases=overflow,sharp_endpoints=endpoints)


def check_bounds():
    rows=[]
    for scale in (81,82,100,243,729,1000,3**16):
        # Integer lower endpoint satisfying scale<r^2.
        low=27
        while low*low<=scale:low+=1
        for r in (low,scale-1,2*scale-1):
            assert scale>=81 and r>=27 and r<2*scale and scale<r*r
            assert scale*scale>r+1 and scale*(scale+1)>2*r+1
            assert 12*r<scale*(scale+1)
            rows.append(dict(D0=scale,r=r))
    for q in range(3,16):
        for f in (4,5,6):
            scale=q**f
            last=(3*(scale-1)-1)//2
            for r in (q**(f-1),last):
                assert scale>=81 and r>=27 and r<2*scale and scale<r*r
    return rows


def check_auxiliary(A,J):
    """Only the exact auxiliary construction; not a full kernel example."""
    d,c=pell_power(A,J);D=A*A-1;m=2*c*J
    f,psi_m=pell_power(A,m)
    i,rem=divmod(D*psi_m,c*c)
    assert rem==0 and i>0
    R=i*c*c
    root,y=pell_power(R,J)
    u,rem=divmod(root,R)
    assert rem==0 and u>c>J
    sign=(-1)**((J-1)//2)
    o,rem_o=divmod(u-sign*c,f)
    j,rem_j=divmod(u-sign*J,c)
    assert rem_o==rem_j==0 and o>0 and j>0
    assert u==j*c+sign*J==o*f+sign*c
    assert R*R==D*(f*f-1)
    assert R*R*(u*u-y*y)==1-y*y
    return dict(A=A,Jmain=J,sign=sign,c_bits=c.bit_length(),f_bits=f.bit_length(),
                u_bits=u.bit_length(),positive_integral_o_j=True,
                exact_both_auxiliary_norms=True,
                scope='Auxiliary construction only; not a full large-index kernel witness')


def verify():
    return dict(status='PASS_GENERAL_SCALE_UNIT_TWO_TERNARY_COMPONENT',
                variants=[verify_certificate(1),verify_certificate(-1)],
                mask=check_mask(),preliminary_cases=check_bounds(),
                exact_auxiliary_cases=[check_auxiliary(A,J) for A in range(2,6) for J in (3,5)],
                canonical_ratio_cases=[previous.check_canonical_ratio(r) for r in (27,28,77)],
                power_schedules={
                    'q4':[['q2','*','q','q'],['D0','*','q2','q2']],
                    'q6':[['q2','*','q','q'],['q3','*','q2','q'],['D0','*','q3','q3']]},
                conditional_component_operations={'q4':45,'q6':46},
                proof='../1980/EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md',
                scope='General-scale power/binomial kernel, two fixed sign choices and direct ternary unit-two mask. Packing, bounds, computation, raw input and halting are separate unless supplied by an independently counted interface.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([(r['sign'],r['operations'],r['primitive_histogram']) for r in result['variants']])
    print(result['mask']['complete_cases'],'mask cases;',len(result['exact_auxiliary_cases']),'auxiliary cases')
