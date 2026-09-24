#!/usr/bin/env python3
"""Exact77 first-plus raw numerical walk from2x to0; no universal claim."""
from pathlib import Path
import itertools
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_unit_two_ternary_kernel as kernel
from explore_native_ternary_ripple import native, central_valuation
from explore_native_ternary_history import power_log

PARAMETERS=['x']
OUTER_NAMES=['q','Jrep','W','H','v','T','F0','F1','G0','G1','FKplus','FKminus','alpha','alphaI']
CORE_NAMES=kernel.previous.CORE_NAMES
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
FIELDS=['FKplus','G0','F0','G1','F1','FKminus']
PREFIX=[
    ('twice_J','+','Jrep','Jrep'),('q_rhs','+','twice_J',1),
    ('geometry_product','*','W','v'),('W_minus_one','-','W',1),
    ('head_geometry','*','H','W_minus_one'),
    ('flag_sum','+','FKplus','FKminus'),('head_rhs','+','twice_J','H'),
    ('top_mask','*',3,'T'),('track_sum','+','F0','F1'),
    ('bound_rhs','+','q','Jrep'),('bound_lhs','+','track_sum','alpha'),
    ('guard0','+','F0','T'),('guard1','+','F1','T'),
    ('raw_A','-','track_sum','twice_J'),('delta','-','FKplus','FKminus'),
    ('input','+','x','x'),('history_product','*','W_minus_one','raw_A'),
    ('control_product','*','W','delta'),('time_partial','+','input','history_product'),
    ('time_lhs','+','time_partial','control_product'),('input_bound','+','input','alphaI'),
]
prior=FIELDS[-1]
for index,field in enumerate(reversed(FIELDS[:-1])):
    product=f'pack_product{index}';target='packed' if index==4 else f'pack_sum{index}'
    PREFIX.extend([(product,'*','q',prior),(target,'+',field,product)]);prior=target
POWERS=[('q2','*','q','q'),('q4','*','q2','q2'),('D0','*','q4','q2')]
SCHEDULE=PREFIX+POWERS+kernel.schedule(1)
EQUALITIES=[('q','q_rhs'),('q','geometry_product'),('head_geometry','twice_J'),
            ('flag_sum','head_rhs'),('top_mask','head_rhs'),('bound_lhs','bound_rhs'),
            ('G0','guard0'),('G1','guard1'),('time_lhs','zero'),('input_bound','W'),
            ('r','packed')]+kernel.EQUALITIES


def source_residuals():
    z=SYM;q,J,W,H=[z[n] for n in ['q','Jrep','W','H']]
    A=z['F0']+z['F1']-2*J;delta=z['FKplus']-z['FKminus']
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS))
    subs={kernel.SYM[n]:z[n] for n in CORE_NAMES};subs[kernel.SYM['D0']]=q**6
    return [q-2*J-1,q-W*z['v'],H*(W-1)-2*J,z['FKplus']+z['FKminus']-2*J-H,
            3*z['T']-2*J-H,z['F0']+z['F1']+z['alpha']-q-J,
            z['G0']-z['F0']-z['T'],z['G1']-z['F1']-z['T'],
            2*z['x']+(W-1)*A+W*delta,2*z['x']+z['alphaI']-W,z['r']-P,
            ]+[p.subs(subs,simultaneous=True) for p in kernel.source_residuals(1)]


def verify_certificate():
    env=dict(SYM);env['zero']=sp.Integer(0)
    hist=baseline.run_schedule(SCHEDULE,env);source=source_residuals();records=[]
    aux_u=SYM['j']*SYM['c']+2*SYM['r']+1
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[18]*(aux_u*aux_u-SYM['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==77 and counts=={'+':39,'*':38}
    assert len(source)==len(EQUALITIES)==21 and len(OUTER_NAMES+CORE_NAMES)==31
    used={v for row in SCHEDULE for v in row[2:]}|{v for pair in EQUALITIES for v in pair}
    assert set(SYM)<=used and all(p.free_symbols<=set(SYM.values()) for p in source)
    q=SYM['q'];J=(q-1)/2
    upper=(3*J-1)*q**5+(3*J-1)*q**4+(4*J-1)*q**3+q*q+(J+1)*q+1
    gap=sp.factor(3*(q**6-1)/2-upper)
    assert sp.expand(gap-(q**5+q**4/2+3*q**3-3*q*q/2-q/2-sp.Rational(5,2)))==0
    t=sp.Symbol('t');coeff=sp.Poly(sp.expand(gap.subs(q,t+3)),t).all_coeffs()
    assert all(c>0 for c in coeff)
    return dict(status='PASS',operations=77,primitive_histogram=counts,histogram=hist,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=31,
                equations=21,primitive_instructions=primitive,equalities=EQUALITIES,residuals=records,
                upper_bound_gap=sp.sstr(gap),positive_gap_coefficients_at_q_equals_t_plus_3=list(map(str,coeff)),
                free_constant_registers={'zero':0})


def split_ternary(value,variant=0):
    first=second=0;place=1
    while value:
        value,digit=divmod(value,3)
        if digit==2:first+=place;second+=place
        elif digit==1:
            if variant%2:first+=place
            else:second+=place
        variant//=2;place*=3
    return first,second


def packed(z):return sum(z[n]*z['q']**i for i,n in enumerate(FIELDS))


def verify_outer(z):
    q,J,W,H,T=[z[n] for n in ['q','Jrep','W','H','T']]
    assert min(z.values())>0
    assert q==2*J+1 and q==W*z['v'] and H*(W-1)==2*J and W>=3 and H<=J
    assert z['FKplus']+z['FKminus']==2*J+H==3*T and T<=J
    S=z['F0']+z['F1'];assert S+z['alpha']==q+J and S<=3*J
    assert z['G0']==z['F0']+T and z['G1']==z['F1']+T
    A=S-2*J;delta=z['FKplus']-z['FKminus'];I=2*z['x']
    assert I+(W-1)*A+W*delta==0 and I+z['alphaI']==W
    assert max(z[n] for n in ['F0','F1','FKplus','FKminus'])<3*J
    assert max(z['G0'],z['G1'])<4*J
    P=packed(z);scale=q**6
    assert P>q**5 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return P


def verify_decoded(z,P):
    q,W,J=[z[n] for n in ['q','W','Jrep']]
    ell=power_log(q,3);m=power_log(W,3)
    assert ell is not None and m and ell%m==0
    height=ell//m
    assert P<q**6 and P%3==2 and native(P,6*ell)
    assert all(z[n]<q and native(z[n],ell) for n in FIELDS)
    A0=z['F0']-J;A1=z['F1']-J;Kp=z['FKplus']-J;Km=z['FKminus']-J
    assert Kp+Km==z['H'] and z['T']==(W//3)*z['H']
    n=2*z['x'];values=[n];signs=[]
    for j in range(height):
        rows=[(word//W**j)%W for word in [A0,A1,Kp,Km]]
        a0,a1,kp,km=rows
        assert a0<W//3 and a1<W//3 and a0+a1<W//3 and a0+a1==n
        assert kp in (0,1) and km==1-kp
        epsilon=kp-km;signs.append(epsilon);n+=epsilon
        assert n>=0;values.append(n)
    assert signs[0]==1 and n==0 and height%2==0 and P%2==0
    assert central_valuation(P)==6*ell
    return dict(x=z['x'],width=m,height=height,values=values,signs=signs)


def canonical(x,signs,variant=0):
    assert x>0 and signs and signs[0]==1
    values=[2*x]
    for epsilon in signs:
        assert epsilon in (-1,1);values.append(values[-1]+epsilon);assert values[-1]>=0
    assert values[-1]==0
    m=1
    while 3**(m-1)<=max(values):m+=1
    W=3**m;height=len(signs);q=W**height;J=(q-1)//2;H=(q-1)//(W-1);T=(W//3)*H
    A0=A1=Kp=Km=0
    for j,(n,epsilon) in enumerate(zip(values,signs)):
        f,s=split_ternary(n,variant+j);A0+=f*W**j;A1+=s*W**j
        if epsilon==1:Kp+=W**j
        else:Km+=W**j
    z=dict(x=x,q=q,Jrep=J,W=W,H=H,v=q//W,T=T,F0=J+A0,F1=J+A1,
           G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
           alpha=q+J-(2*J+A0+A1),alphaI=W-2*x)
    P=verify_outer(z);verify_decoded(z,P);return z,P


def verify_regression():
    prepower=canonical_count=split_variants=0;samples=[]
    # These tuples verify the paid polynomial range without assuming powers.
    for q in range(3,24,2):
        J=(q-1)//2
        for W in range(3,q+1,2):
            if q%W or (q-1)%(W-1):continue
            H=(q-1)//(W-1)
            if (2*J+H)%3:continue
            T=(2*J+H)//3
            for f0 in range(1,3*J):
                for f1 in range(1,3*J-f0+1):
                    for kp in range(1,2*J+H):
                        km=2*J+H-kp;A=f0+f1-2*J
                        I=-(W-1)*A-W*(kp-km)
                        if I<=0 or I%2 or I>=W:continue
                        z=dict(x=I//2,q=q,Jrep=J,W=W,H=H,v=q//W,T=T,F0=f0,F1=f1,
                               G0=f0+T,G1=f1+T,FKplus=kp,FKminus=km,
                               alpha=q+J-f0-f1,alphaI=W-I)
                        verify_outer(z);prepower+=1
    for x in range(1,4):
        for height in range(2*x+2,13,2):
            for tail in itertools.product((-1,1),repeat=height-1):
                signs=(1,)+tail;n=2*x;okay=True
                for epsilon in signs:
                    n+=epsilon
                    if n<0:okay=False;break
                if not okay or n:continue
                z,P=canonical(x,signs);canonical_count+=1
                if len(samples)<6:samples.append(dict(**verify_decoded(z,P),outer=z,packed=P,scale=z['q']**6))
                if canonical_count%17==0:
                    canonical(x,signs,7);split_variants+=1
    # A prefix +1,-1 preserves any raw starting value and has even length.
    prefix_cases=0
    for x in range(1,31):
        signs=(1,-1)+(-1,)*(2*x)
        z,P=canonical(x,signs);prefix_cases+=1
        assert z['x']==x and P%2==0
    return dict(prepower_positive_tuples=prepower,canonical_walks=canonical_count,
                alternative_track_splits=split_variants,prefix_cleanup_families=prefix_cases,samples=samples,
                scope='Paid prepower range and exact finite nonnegative walks from2x to0, firststep+. No universal control or enormous Pell coordinates are tested.')


def verify():
    return dict(status='PASS_RAW_TERNARY_FIRST_PLUS_ZERO_TARGET',arithmetic=verify_certificate(),
                regression=verify_regression(),proof='../1980/EXPLORATION_RAW_TERNARY_ZERO_TARGET.md',
                scope='Complete77 positive-variable component exposing a first-plus mixed-control walk fromraw2x to0. Allpositivex admit some suchwalk; a separate machine control/halting construction is required.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['regression'].items() if k not in ('samples','scope')})
