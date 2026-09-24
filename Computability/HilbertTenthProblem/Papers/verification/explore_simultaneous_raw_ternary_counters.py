#!/usr/bin/env python3
"""Safe simultaneous raw-register histories:80 operations(k2),81(k3)."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_raw_ternary_zero_target as old
from explore_native_ternary_ripple import native,central_valuation
from explore_native_ternary_history import power_log

PARAMETERS=['x'];OUTER_NAMES=old.OUTER_NAMES+['R','Htime'];CORE_NAMES=old.CORE_NAMES
SYM={n:sp.Symbol(n) for n in PARAMETERS+OUTER_NAMES+CORE_NAMES}
FIELDS=old.FIELDS


def schedule(registers):
    assert registers in (2,3)
    prefix=[]
    for row in old.PREFIX:
        if row[0]=='head_geometry':
            prefix.append(('R_minus_one','-','R',1))
            row=('head_geometry','*','H','R_minus_one')
        prefix.append(row)
    if registers==2:prefix.append(('W_rhs','*','R','R'))
    else:prefix.extend([('R2','*','R','R'),('W_rhs','*','R2','R')])
    prefix.append(('time_head_product','*','Htime','W_minus_one'))
    return prefix+old.POWERS+old.kernel.schedule(1)


def equalities():
    pairs=list(old.EQUALITIES);pairs[9]=('input_bound','R')
    return pairs+[('W','W_rhs'),('time_head_product','twice_J')]


def source_residuals(registers):
    source=[p.subs({old.SYM[n]:SYM[n] for n in old.SYM},simultaneous=True) for p in old.source_residuals()]
    source[2]=SYM['H']*(SYM['R']-1)-2*SYM['Jrep']
    source[9]=2*SYM['x']+SYM['alphaI']-SYM['R']
    return source+[SYM['W']-SYM['R']**registers,SYM['Htime']*(SYM['W']-1)-2*SYM['Jrep']]


def verify_certificate(registers):
    instructions=schedule(registers);env=dict(SYM);env['zero']=sp.Integer(0)
    hist=baseline.run_schedule(instructions,env);source=source_residuals(registers);pairs=equalities();records=[]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for index,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[18]*(u*u-SYM['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(instructions,env)
    expected=78+registers
    assert len(primitive)==expected and counts=={'+':40,'*':38+registers}
    assert len(source)==len(pairs)==23 and len(OUTER_NAMES+CORE_NAMES)==33
    used={v for row in instructions for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used and all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',registers=registers,operations=expected,primitive_histogram=counts,histogram=hist,
                parameters=PARAMETERS,positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=33,
                equations=23,primitive_instructions=primitive,equalities=pairs,residuals=records,
                free_constant_registers={'zero':0})


def verify_outer(z,registers):
    q,J,R,W,H,Htime,T=[z[n] for n in ['q','Jrep','R','W','H','Htime','T']]
    assert min(z.values())>0
    assert q==2*J+1 and W==R**registers and q==W*z['v']
    assert H*(R-1)==Htime*(W-1)==2*J and R>=3 and H<=J
    assert z['FKplus']+z['FKminus']==2*J+H==3*T and T<=J
    S=z['F0']+z['F1'];assert S+z['alpha']==q+J and S<=3*J
    assert z['G0']==z['F0']+T and z['G1']==z['F1']+T
    A=S-2*J;delta=z['FKplus']-z['FKminus'];I=2*z['x']
    assert I+(W-1)*A+W*delta==0 and I+z['alphaI']==R
    assert max(z[n] for n in ['F0','F1','FKplus','FKminus'])<3*J
    assert max(z['G0'],z['G1'])<4*J
    P=old.packed(z);scale=q**6
    assert P>q**5 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return P


def verify_decoded(z,P,registers):
    q,R,W,J=[z[n] for n in ['q','R','W','Jrep']]
    m=power_log(R,3);ell=power_log(q,3)
    assert m and ell and ell%(registers*m)==0
    height=ell//(registers*m)
    assert W==R**registers and z['Htime']==(q-1)//(W-1)
    assert z['H']==(q-1)//(R-1) and z['T']==(R//3)*z['H']
    assert P<q**6 and P%3==2 and native(P,6*ell)
    assert all(z[n]<q and native(z[n],ell) for n in FIELDS)
    raw=[z[n]-J for n in ['F0','F1','FKplus','FKminus']]
    assert raw[2]+raw[3]==z['H']
    values=[2*z['x']]+[0]*(registers-1);history=[list(values)];controls=[]
    for time in range(height):
        signs=[]
        for index in range(registers):
            block=registers*time+index
            a0,a1,kp,km=[(word//R**block)%R for word in raw]
            assert a0+a1==values[index] and 0<=values[index]<R//3
            assert a0<R//3 and a1<R//3 and kp in (0,1) and km==1-kp
            signs.append(kp-km)
        for index,epsilon in enumerate(signs):values[index]+=epsilon
        assert min(values)>=0;history.append(list(values));controls.append(signs)
    assert values==[0]*registers and controls[0][0]==1
    assert all(epsilon==1 for epsilon in controls[0])
    assert height%2==0 and P%2==0 and z['H']%2==0
    assert central_valuation(P)==6*ell
    return dict(x=z['x'],registers=registers,counter_digit_width=m,height=height,values=history,controls=controls)


def canonical(x,controls,registers,variant=0):
    assert x>0 and controls and len(controls[0])==registers and controls[0][0]==1
    values=[2*x]+[0]*(registers-1);history=[list(values)]
    for signs in controls:
        assert len(signs)==registers and all(e in (-1,1) for e in signs)
        values=[a+e for a,e in zip(values,signs)];assert min(values)>=0
        history.append(list(values))
    assert values==[0]*registers
    m=1
    while 3**(m-1)<=max(max(row) for row in history):m+=1
    R=3**m;W=R**registers;height=len(controls);q=W**height;J=(q-1)//2
    H=(q-1)//(R-1);Htime=(q-1)//(W-1);T=(R//3)*H
    A0=A1=Kp=Km=0
    for time,signs in enumerate(controls):
        for index,epsilon in enumerate(signs):
            block=registers*time+index
            a0,a1=old.split_ternary(history[time][index],variant+block)
            A0+=a0*R**block;A1+=a1*R**block
            if epsilon==1:Kp+=R**block
            else:Km+=R**block
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,Htime=Htime,v=q//W,T=T,
           F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
           alpha=q+J-(2*J+A0+A1),alphaI=R-2*x)
    P=verify_outer(z,registers);verify_decoded(z,P,registers);return z,P


def admissible_signs(start,height,first_plus=False):
    result=[]
    for signs in product((-1,1),repeat=height):
        if first_plus and signs[0]!=1:continue
        n=start;okay=True
        for epsilon in signs:
            n+=epsilon
            if n<0:okay=False;break
        if okay and n==0:result.append(signs)
    return result


def verify_regression(registers):
    joint=longer=variants=0;samples=[]
    for height in (4,6):
        first=admissible_signs(2,height,True);others=admissible_signs(0,height)
        for words in product(first,*([others]*(registers-1))):
            controls=list(zip(*words));z,P=canonical(1,controls,registers);joint+=1
            if len(samples)<4:samples.append(dict(**verify_decoded(z,P,registers),outer=z,packed=P,scale=z['q']**6))
            if joint%13==0:canonical(1,controls,registers,7);variants+=1
    for x in range(1,16):
        first=(1,-1)+(-1,)*(2*x);height=len(first)
        alternating=(1,-1)*(height//2);mountain=(1,)*(height//2)+(-1,)*(height//2)
        for patterns in product((alternating,mountain),repeat=registers-1):
            controls=list(zip(first,*patterns));canonical(x,controls,registers);longer+=1
    # Exact signed base-R coefficient induction, including zero input blocks,
    # is separately checked for all small values and +/-1 controls.
    local=0
    for R in (3,9,27,81):
        for a in range(R//3):
            for b in range(R//3):
                for epsilon in (-1,1):
                    coeff=a+epsilon-b
                    assert abs(coeff)<R and (coeff%R==0)==(b==a+epsilon)
                    local+=1
    return dict(registers=registers,complete_small_joint_walks=joint,
                alternative_track_splits=variants,longer_cleanup_families=longer,
                signed_local_transition_cases=local,samples=samples,
                scope='Complete joint control sequences for x1 and heights4,6; longer cleanup/excursion families for x1..15. No machine control or huge Pell tuples are numerically instantiated.')


def verify():
    return dict(status='PASS_SIMULTANEOUS_RAW_REGISTER_HISTORIES',
                variants=[dict(arithmetic=verify_certificate(k),regression=verify_regression(k)) for k in (2,3)],
                proof='../1980/EXPLORATION_SIMULTANEOUS_RAW_TERNARY_COUNTERS.md',
                scope='Counted bounded synchronous raw +/-1 register histories, initial[2x,0,...], finalallzero. Neither universalprogram compilation nor rawtwo-counteruniversality is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for row in result['variants']:
        print(row['arithmetic']['registers'],row['arithmetic']['operations'],row['arithmetic']['primitive_histogram'])
        print({k:v for k,v in row['regression'].items() if k not in ('samples','scope')})
