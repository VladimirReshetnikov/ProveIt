#!/usr/bin/env python3
"""Exact62 bounded native ripple retaining the C and E masks."""
from pathlib import Path
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_base_three_positive_kernel as base
import explore_unit_two_ternary_kernel as unit

PARAMETERS=['q','FA','FB']
OUTER_NAMES=['Hrep','FC','FE','alpha']
CORE_NAMES=base.CORE_NAMES
SYM={name:sp.Symbol(name) for name in PARAMETERS+OUTER_NAMES+CORE_NAMES}


def schedule(borrow=False):
    X,Y=('FB','FA') if borrow else ('FA','FB')
    prefix=[
        ('Hplus1','+','Hrep',1),('q_rhs','+','Hplus1','Hrep'),
        ('S','+',X,'FE'),('local_lhs','+','S','FE'),
        ('local_pair','+',Y,'FC'),('local_rhs','+','local_pair','Hrep'),
        ('three_E','*',3,'FE'),('twice_C','+','FC','FC'),
        ('seed_rhs','+','twice_C','Hplus1'),
        ('bound_rhs','+','q','Hrep'),('bound','+','S','alpha'),
        ('pack0','*','q','FE'),('pack1','+','FB','pack0'),
        ('pack2','*','q','pack1'),('pack3','+','FA','pack2'),
        ('pack4','*','q','pack3'),('packed','+','FC','pack4'),
        ('q2','*','q','q'),('D0','*','q2','q2'),
    ]
    equalities=[('q','q_rhs'),('three_E','seed_rhs'),('local_lhs','local_rhs'),
                ('bound','bound_rhs'),('r','packed')]+unit.EQUALITIES
    return prefix+unit.schedule(-1),equalities


def source_residuals(borrow=False):
    z=SYM
    q,FA,FB,H,FC,FE,alpha=[z[n] for n in PARAMETERS+OUTER_NAMES]
    X,Y=(FB,FA) if borrow else (FA,FB)
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in CORE_NAMES]
    packed=FC+q*FA+q*q*FB+q**3*FE
    U,Yp=w*q**4,s*q**4;Q=U*Yp*Yp;disc=a*a+6*a+8;aux_u=j*c-2*r-1
    return [q-2*H-1,3*FE-2*FC-H-1,X+2*FE-Y-FC-H,
            X+FE+alpha-q-H,r-packed,
            Q*(Q+1)*k*k-tau*(tau+1),c-Yp*k-eta,k-eta-zeta,
            k-r-1-h*U*Yp,a-Yp*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
            disc*(f*f-1)*(aux_u*aux_u-y*y)-(1-y*y),aux_u-o*f+c]


def verify_certificate(borrow=False):
    instructions,equalities=schedule(borrow);env=dict(SYM)
    histogram=baseline.run_schedule(instructions,env)
    source=source_residuals(borrow)
    u=SYM['j']*SYM['c']-2*SYM['r']-1
    correction=source[12]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(equalities,source)):
        actual=sp.expand(env[left]-env[right]);extra=correction if index==13 else sp.Integer(0)
        assert sp.expand(actual-residual-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitives,counts=verify_primitives(instructions,env)
    assert len(primitives)==62 and counts=={'+':31,'*':31}
    assert len(records)==len(source)==len(equalities)==15
    assert len(OUTER_NAMES+CORE_NAMES)==21
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    used={x for row in instructions for x in row[2:]}|{x for pair in equalities for x in pair}
    assert set(SYM)<=used
    return dict(mode='borrow' if borrow else 'increment',arithmetic_status='PASS',
                operations=62,primitive_histogram=counts,histogram=histogram,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=21,equations=15,primitive_instructions=primitives,
                equalities=equalities,residuals=records,fixed_kernel_sign=-1)


def code(n):
    result=0;place=1
    while n:
        result+=(n&1)*place;n>>=1;place*=3
    return result


def decode(n,width):
    if n<0:return None
    result=0
    for j in range(width):
        n,d=divmod(n,3)
        if d>1:return None
        result+=d<<j
    return None if n else result


def native(n,width):return decode(n-(3**width-1)//2,width) is not None


def verify_outer(q,FA,FB,FC,FE,H,alpha,borrow=False):
    X,Y=(FB,FA) if borrow else (FA,FB)
    assert min(q,FA,FB,FC,FE,H,alpha)>0 and q==2*H+1
    assert 3*FE==2*FC+H+1
    assert X+2*FE==Y+FC+H
    assert X+FE+alpha==q+H
    assert X+FE<=3*H and max(FA,FB,FE)<3*H and FC<4*H
    packed=FC+q*FA+q*q*FB+q**3*FE;scale=q**4;r=packed
    assert q**3<packed and 2*packed<3*(scale-1)
    assert scale>=81 and r>=27 and r<2*scale and scale<r*r
    assert scale*scale>r+1 and scale*(scale+1)>2*r+1
    assert 12*r<scale*(scale+1)
    assert packed%2==1
    return packed,r


def positive_candidates(q):
    H=(q-1)//2
    for FE in range(1,3*H):
        numerator=3*FE-H-1
        if numerator<=0 or numerator%2:continue
        FC=numerator//2
        for X in range(1,3*H-FE+1):
            numerator_y=2*X+FE-H+1
            if numerator_y<=0 or numerator_y%2:continue
            Y=numerator_y//2
            alpha=q+H-X-FE
            yield X,Y,FC,FE,H,alpha


def verify_regression():
    prepower=enumerated=accepted=canonical=boundary=0
    samples=[];false_field_overflows=0
    for q in range(3,32,2):
        for X,Y,FC,FE,H,alpha in positive_candidates(q):
            for borrow in (False,True):
                FA,FB=(Y,X) if borrow else (X,Y)
                verify_outer(q,FA,FB,FC,FE,H,alpha,borrow)
                prepower+=1
    for width in range(1,5):
        q=3**width;H=(q-1)//2
        for X,Y,FC,FE,H,alpha in positive_candidates(q):
            for borrow in (False,True):
                enumerated+=1
                FA,FB=(Y,X) if borrow else (X,Y)
                packed,r=verify_outer(q,FA,FB,FC,FE,H,alpha,borrow)
                val=unit.valuation(r)
                if val<4*width:
                    false_field_overflows+=max(FA,FB,FC,FE)>=q
                    continue
                accepted+=1
                assert packed<q**4 and unit.mask_expected(packed,4*width)
                assert all(native(F,width) and F<q for F in (FA,FB,FC,FE))
                old,new=decode(FA-H,width),decode(FB-H,width)
                assert new==(old-1 if borrow else old+1)
                assert val==4*width
                if len(samples)<8:samples.append(dict(width=width,borrow=borrow,
                    FA=FA,FB=FB,FC=FC,FE=FE,alpha=alpha,P0=packed,r=r))
    assert accepted==52
    for width in range(1,9):
        q=3**width;H=(q-1)//2
        for borrow in (False,True):
            inputs=range(1,2**width) if borrow else range(2**width-1)
            for raw in inputs:
                k=0
                while ((raw>>k)&1)==(0 if borrow else 1):k+=1
                C=(3**(k+1)-1)//2;E=3**k
                FA=H+code(raw);FB=H+code(raw-1 if borrow else raw+1)
                FC,FE=H+C,H+E
                X=FB if borrow else FA
                alpha=q+H-X-FE
                packed,r=verify_outer(q,FA,FB,FC,FE,H,alpha,borrow)
                assert unit.mask_expected(packed,4*width) and unit.valuation(r)==4*width
                assert native(packed,4*width) and packed%3==2
                assert alpha>=1
                if width==1:assert packed==(71 if borrow else 77)
                canonical+=1;boundary+=alpha==1
    return dict(prepower_positive_outer_tuples=prepower,
                complete_positive_candidate_pairs=enumerated,
                accepted_complete_candidates=accepted,
                rejected_supplied_field_overflows=false_field_overflows,
                canonical_ripples=canonical,canonical_alpha_one_cases=boundary,
                samples=samples,
                scope='All positive source-compatible outer candidates at widths1..4 and canonical ripples through width8. The full odd-sign Pell witnesses exist by theorem, not by a numerical materialization here.')


def verify():
    return dict(status='PASS_UNIT_TWO_TERNARY_BOUNDED_RIPPLE_COMPONENT',
                variants=[verify_certificate(False),verify_certificate(True)],
                regression=verify_regression(),
                proof='../1980/EXPLORATION_UNIT_TWO_TERNARY_RIPPLE.md',
                scope='Complete62-operation bounded increment/borrow relation on native ternary codes of binary counters. All range and parity conditions follow from counted equations. No raw-number conversion, universal machine history or halting interface is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for row in result['variants']:print(row['mode'],row['operations'],row['primitive_histogram'],row['equations'])
    print({k:v for k,v in result['regression'].items() if k not in ('samples','scope')})
