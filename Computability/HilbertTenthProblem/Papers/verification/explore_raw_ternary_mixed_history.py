#!/usr/bin/env python3
"""Exact82 raw nonnegative counter history, with typed +/-1 row controls."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_parity_free_pell_kernel as kernel
from explore_native_ternary_ripple import native,central_valuation
from explore_native_ternary_history import power_log

PARAMETERS=['I','Fplus']
OUTER_NAMES=['q','F0','F1','T0','T1','FKp','FKm','Jrep','alpha','W','H','T','v','alphaI']
CORE_NAMES=['a','c','d','f','h','i','j','k','o','r','s','w','tau','eta','zeta','ga','y_aux','u']
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
FIELDS=['T0','F0','T1','F1','FKp','FKm']
PREFIX=[
    ('twice_J','+','Jrep','Jrep'),('q_rhs','+','twice_J',1),
    ('S','+','F0','F1'),('bound_lhs','+','S','alpha'),('bound_rhs','+','q','Jrep'),
    ('guard0','+','F0','T'),('guard1','+','F1','T'),
    ('geometry_product','*','W','v'),('W_minus_one','-','W',1),
    ('row_mask_product','*','H','W_minus_one'),
    ('head_lhs','+','FKp','FKm'),('head_rhs','+','twice_J','H'),
    ('three_T','*',3,'T'),('raw_A','-','S','twice_J'),
    ('delta_K','-','FKp','FKm'),('space_product','*','W_minus_one','raw_A'),
    ('control_product','*','W','delta_K'),('time_partial','+','space_product','control_product'),
    ('time_initial','+','I','time_partial'),('time_lhs','+','time_initial','q'),
    ('time_rhs','*','q','Fplus'),('input_bound','+','I','alphaI'),
]
prior=FIELDS[-1]
for index,field in enumerate(reversed(FIELDS[:-1])):
    product_name=f'pack_product{index}';target='packed' if index==4 else f'pack_sum{index}'
    PREFIX += [(product_name,'*','q',prior),(target,'+',field,product_name)]
    prior=target
MASK=[('q2','*','q','q'),('q4','*','q2','q2'),('L','*','q4','q2'),
      ('D0','*',3,'L'),('three_P','*',3,'packed'),('r_rhs','+','three_P',2)]
SCHEDULE=PREFIX+MASK+kernel.SCHEDULE
EQUALITIES=[('q','q_rhs'),('bound_lhs','bound_rhs'),('T0','guard0'),('T1','guard1'),
    ('q','geometry_product'),('row_mask_product','twice_J'),('head_lhs','head_rhs'),
    ('three_T','head_rhs'),('time_lhs','time_rhs'),('input_bound','W'),('r','r_rhs')]+kernel.EQUALITIES


def source_residuals():
    z=SYM
    I,Fplus=z['I'],z['Fplus'];q,J,W,H,T=z['q'],z['Jrep'],z['W'],z['H'],z['T']
    F0,F1,T0,T1,Kp,Km=[z[n] for n in ['F0','F1','T0','T1','FKp','FKm']]
    S=F0+F1;P=sum(z[n]*q**i for i,n in enumerate(FIELDS));scale=3*q**6
    core=kernel.source_residuals();subs={kernel.SYM[n]:z[n] for n in CORE_NAMES}
    subs[kernel.SYM['D0']]=scale
    return [q-2*J-1,S+z['alpha']-q-J,T0-F0-T,T1-F1-T,q-W*z['v'],
        H*(W-1)-q+1,Kp+Km-2*J-H,3*T-2*J-H,
        I+(W-1)*(S-2*J)+W*(Kp-Km)+q-q*Fplus,
        I+z['alphaI']-W,z['r']-3*P-2]+[p.subs(subs,simultaneous=True) for p in core]


def verify_certificate():
    env=dict(SYM);hist=baseline.run_schedule(SCHEDULE,env);source=source_residuals();records=[]
    for index,((left,right),p) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[0] if index==5 else source[18]*(SYM['u']**2-SYM['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(SCHEDULE,env)
    assert len(primitive)==82 and counts=={'+':40,'*':42}
    assert len(source)==len(EQUALITIES)==22 and len(OUTER_NAMES+CORE_NAMES)==32
    used={x for row in SCHEDULE for x in row[2:]}|{x for pair in EQUALITIES for x in pair}
    assert set(SYM)<=used and all(p.free_symbols<=set(SYM.values()) for p in source)
    q=SYM['q'];J=(q-1)/2
    upper=(3*J-1)*(q**3+q*q)+q+1+J*(1+q*q)+q**4+(3*J-1)*q**5
    gap=sp.factor(3*(q**6-1)/2-upper)
    coefficients=sp.Poly(sp.expand(gap.subs(q,sp.Symbol('t')+3)),sp.Symbol('t')).all_coeffs()
    assert all(c>0 for c in coefficients)
    return dict(arithmetic_status='PASS',operations=82,primitive_histogram=counts,histogram=hist,
        parameters=PARAMETERS,parameter_domains={'I':'nonnegative integer, including literal zero','Fplus':'positive integer; raw output is Fplus-1'},
        positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=32,equations=22,
        primitive_instructions=primitive,equalities=EQUALITIES,residuals=records,
        packing_upper_gap=sp.sstr(gap),gap_coefficients_at_q_equals_t_plus_3=[str(c) for c in coefficients])


def outer_values(q,W,F0,F1,Kp):
    if q%2==0 or W<2 or q%W or (q-1)%(W-1):return None
    J=(q-1)//2;H=(q-1)//(W-1)
    if (2*J+H)%3:return None
    T=(2*J+H)//3;Km=2*J+H-Kp;S=F0+F1;alpha=q+J-S
    if min(F0,F1,Kp,Km,alpha)<=0:return None
    rawA=S-2*J;delta=Kp-Km
    I=(-(W-1)*rawA-W*delta)%q
    if not 0<=I<W:return None
    Fplus=(I+(W-1)*rawA+W*delta+q)//q
    if Fplus<=0:return None
    return dict(q=q,W=W,H=H,T=T,v=q//W,F0=F0,F1=F1,T0=F0+T,T1=F1+T,
                FKp=Kp,FKm=Km,Jrep=J,alpha=alpha,I=I,Fplus=Fplus,alphaI=W-I)


def verify_outer(z):
    assert z['I']>=0 and all(value>0 for key,value in z.items() if key!='I')
    q,W,H,T,J=[z[n] for n in ['q','W','H','T','Jrep']]
    S=z['F0']+z['F1'];rawA=S-2*J;delta=z['FKp']-z['FKm']
    assert q==2*J+1 and q==W*z['v'] and H*(W-1)==2*J and 3*T==2*J+H
    assert z['FKp']+z['FKm']==2*J+H
    assert z['T0']==z['F0']+T and z['T1']==z['F1']+T
    assert S+z['alpha']==q+J and z['I']+z['alphaI']==W
    assert z['I']+(W-1)*rawA+W*delta+q==q*z['Fplus']
    assert W>=3 and 0<H<=J and 0<T<=J
    assert S<=3*J and max(z['F0'],z['F1'],z['FKp'],z['FKm'])<3*J
    assert max(z['T0'],z['T1'])<4*J<2*q
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));L=q**6;scale=3*L;r=3*P+2
    assert q**5<P and 2*P<3*(L-1)
    assert scale>=81 and r>=27 and r<2*scale and scale<r*r
    assert scale*scale>r+1 and scale*(scale+1)>2*r+1 and 12*r<scale*(scale+1)
    return P,r


def boolean(value):
    if value<0:return False
    while value:
        value,d=divmod(value,3)
        if d>1:return False
    return True


def verify_decoded(z,P,r):
    q,W,J=[z[n] for n in ['q','W','Jrep']];ell=power_log(q,3);m=power_log(W,3)
    assert ell and m and ell%m==0
    height=ell//m;H=z['H'];T=z['T']
    assert T==W//3*H and boolean(H) and boolean(T)
    assert P<q**6 and native(P,6*ell) and central_valuation(r)==6*ell+1
    assert all(0<z[n]<q and native(z[n],ell) for n in FIELDS)
    raw0,raw1=z['F0']-J,z['F1']-J;Kp,Km=z['FKp']-J,z['FKm']-J
    assert Kp+Km==H and boolean(Kp) and boolean(Km)
    rows=[];current=z['I'];A=raw0+raw1
    for t in range(height):
        a0=(raw0//W**t)%W;a1=(raw1//W**t)%W
        assert a0<W//3 and a1<W//3
        assert a0+a1<W//3
        n=(A//W**t)%W;plus=(Kp//W**t)%W;minus=(Km//W**t)%W
        assert plus in (0,1) and minus==1-plus and n==current
        target=n+plus-minus
        assert target>=0
        rows.append(dict(source=n,delta=plus-minus,target=target))
        current=target
    assert current==z['Fplus']-1
    return rows


def split_ternary(n,phase=0):
    a=b=0;place=1;i=0
    while n:
        n,digit=divmod(n,3)
        if digit==2:a+=place;b+=place
        elif digit==1:
            if (i+phase)%2:a+=place
            else:b+=place
        place*=3;i+=1
    return a,b


def canonical(m,controls,initial):
    height=len(controls);W=3**m;q=W**height;J=(q-1)//2;H=(q-1)//(W-1);T=W//3*H
    raw0=raw1=Kp=Km=0;current=initial
    for t,delta in enumerate(controls):
        assert delta in (-1,1) and 0<=current<W//3
        a,b=split_ternary(current,t)
        assert a+b==current and boolean(a) and boolean(b)
        raw0+=a*W**t;raw1+=b*W**t
        if delta==1:Kp+=W**t
        else:Km+=W**t
        current+=delta
        assert current>=0
    z=dict(q=q,W=W,H=H,T=T,v=q//W,Jrep=J,F0=J+raw0,F1=J+raw1,
           T0=J+raw0+T,T1=J+raw1+T,FKp=J+Kp,FKm=J+Km,
           alpha=J+1-raw0-raw1,I=initial,Fplus=current+1,alphaI=W-initial)
    P,r=verify_outer(z);verify_decoded(z,P,r)
    return z,P,r


def verify_regression():
    preliminary=candidates=accepted=canonical_count=zero_input=zero_output=final_top=odd=even=0;samples=[]
    for q in range(3,22,2):
        J=(q-1)//2
        for W in range(2,q+1):
            if q%W or (q-1)%(W-1):continue
            H=(q-1)//(W-1)
            if (2*J+H)%3:continue
            for F0 in range(1,3*J):
                for F1 in range(1,3*J-F0+1):
                    for Kp in range(1,2*J+H):
                        z=outer_values(q,W,F0,F1,Kp)
                        if z is None:continue
                        verify_outer(z);preliminary+=1
    for ell in range(1,4):
        q=3**ell;J=(q-1)//2
        for m in range(1,ell+1):
            if ell%m:continue
            W=3**m;H=(q-1)//(W-1)
            for F0 in range(1,3*J):
                for F1 in range(1,3*J-F0+1):
                    for Kp in range(1,2*J+H):
                        candidates+=1
                        z=outer_values(q,W,F0,F1,Kp)
                        if z is None:continue
                        P,r=verify_outer(z)
                        if central_valuation(r)<6*ell+1:continue
                        rows=verify_decoded(z,P,r);accepted+=1
                        if len(samples)<8:samples.append(dict(outer=z,rows=rows,packed=P,index=r))
    for m in range(1,6):
        cap=3**(m-1)
        for height in range(1,5):
            for controls in product((-1,1),repeat=height):
                for initial in range(cap):
                    current=initial;valid=True
                    for delta in controls:
                        if not 0<=current<cap or current+delta<0:valid=False;break
                        current+=delta
                    if not valid:continue
                    z,P,r=canonical(m,controls,initial)
                    canonical_count+=1;zero_input+=initial==0;zero_output+=current==0
                    final_top+=current==cap;odd+=r%2;even+=r%2==0
    assert zero_input and zero_output and final_top and odd and even
    return dict(prepower_positive_tuples=preliminary,complete_candidates=candidates,
        accepted_complete_candidates=accepted,canonical_histories=canonical_count,
        zero_input_histories=zero_input,zero_output_histories=zero_output,
        final_at_row_guard_limit=final_top,odd_indices=odd,even_indices=even,samples=samples,
        scope='All prepower positive outer tuples at oddq3..21 within source bounds; complete total widths1..3; all canonical +/-1 words of heights1..4 and guarded raw inputs of row widths1..5. No enormous full Pell tuple instantiated.')


def verify():
    return dict(status='PASS_RAW_TERNARY_MIXED_COUNTER_HISTORY',arithmetic=verify_certificate(),
        regression=verify_regression(),proof='../1980/EXPLORATION_RAW_TERNARY_MIXED_HISTORY.md',
        scope='Complete raw nonnegative +/-1 counter-history interface with typed head controls and positive output adapter. RawinputI requires no radix conversion. Program selection, conditional branching and a universal compiler remain separate.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['regression'])
