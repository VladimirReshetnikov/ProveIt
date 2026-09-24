#!/usr/bin/env python3
"""Factored raw-register histories with parity-derived frames:76/77/78."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
import explore_raw_ternary_zero_target as single
import explore_simultaneous_raw_ternary_counters as safe
from explore_native_ternary_ripple import native,central_valuation
from explore_native_ternary_history import power_log


def symbols(registers):
    outer=single.OUTER_NAMES+(['R'] if registers>1 else [])
    return {n:sp.Symbol(n) for n in ['x']+outer+single.CORE_NAMES},outer


def schedule(registers):
    assert registers in (1,2,3)
    old=single.SCHEDULE if registers==1 else safe.schedule(registers)
    result=[]
    remove={'history_product','control_product','time_partial','time_head_product'}
    if registers>1:remove.add('W_minus_one')
    for row in old:
        if row[0] in remove:continue
        if row[0]=='time_lhs':
            result.extend([('next_A','+','raw_A','delta'),('time_lhs','*','W','next_A'),
                           ('time_rhs','-','raw_A','input')])
        else:result.append(row)
    return result


def equalities(registers):
    pairs=list(single.EQUALITIES if registers==1 else safe.equalities()[:-1])
    pairs[8]=('time_lhs','time_rhs');return pairs


def source_residuals(registers):
    z,_=symbols(registers)
    source=single.source_residuals() if registers==1 else safe.source_residuals(registers)[:-1]
    old_symbols=single.SYM if registers==1 else safe.SYM
    subst={old_symbols[n]:z[n] for n in z}
    return [p.subs(subst,simultaneous=True) for p in source]


def verify_certificate(registers):
    z,outer=symbols(registers);env=dict(z)
    instructions=schedule(registers);hist=baseline.run_schedule(instructions,env)
    source=source_residuals(registers);pairs=equalities(registers);records=[]
    u=z['j']*z['c']+2*z['r']+1
    for index,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[18]*(u*u-z['y_aux']**2) if index==19 else 0
        assert sp.expand(actual-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=verify_primitives(instructions,env)
    assert len(primitive)==75+registers and counts=={'+':39,'*':36+registers}
    assert len(source)==len(pairs)==(21 if registers==1 else 22)
    assert len(outer+single.CORE_NAMES)==(31 if registers==1 else 32)
    assert all(p.free_symbols<=set(z.values()) for p in source)
    used={v for row in instructions for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(z)<=used
    assert not any(row[0]=='time_head_product' for row in instructions)
    if registers>1:assert not any('W_minus_one' in row for row in instructions)
    W,A,delta,I=sp.symbols('W A delta I')
    assert sp.expand(W*(A+delta)-(A-I)-(I+(W-1)*A+W*delta))==0
    return dict(status='PASS',registers=registers,operations=len(primitive),primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=outer+single.CORE_NAMES,
                unknown_count=len(outer+single.CORE_NAMES),equations=len(source),
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                time_identity='W*(A+delta)-(A-I) = I+(W-1)*A+W*delta')


def verify_outer(z,registers):
    if registers==1:return single.verify_outer(z)
    q,J,R,W,H,T=[z[n] for n in ['q','Jrep','R','W','H','T']]
    assert min(z.values())>0
    assert q==2*J+1 and W==R**registers and q==W*z['v']
    assert H*(R-1)==2*J and R>=3 and H<=J
    assert z['FKplus']+z['FKminus']==2*J+H==3*T and T<=J
    S=z['F0']+z['F1'];assert S+z['alpha']==q+J and S<=3*J
    assert z['G0']==z['F0']+T and z['G1']==z['F1']+T
    A=S-2*J;delta=z['FKplus']-z['FKminus'];I=2*z['x']
    assert W*(A+delta)==A-I and I+z['alphaI']==R
    P=single.packed(z);scale=q**6
    assert P>q**5 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return P


def verify_decoded(z,P,registers):
    if registers==1:return single.verify_decoded(z,P)
    q,R,W,J=[z[n] for n in ['q','R','W','Jrep']]
    m=power_log(R,3);ell=power_log(q,3)
    assert m and ell and ell%m==0
    blocks=ell//m;assert blocks>=registers and W==R**registers
    assert z['H']==(q-1)//(R-1) and z['T']==(R//3)*z['H']
    assert P<q**6 and P%3==2 and native(P,6*ell)
    assert all(z[n]<q and native(z[n],ell) for n in single.FIELDS)
    raw=[z[n]-J for n in ['F0','F1','FKplus','FKminus']]
    assert raw[2]+raw[3]==z['H']
    lengths=[]
    for index in range(registers):
        value=2*z['x'] if index==0 else 0;length=0
        for block in range(index,blocks,registers):
            a0,a1,kp,km=[(word//R**block)%R for word in raw]
            assert a0+a1==value and 0<=value<R//3
            assert kp in (0,1) and km==1-kp
            value+=kp-km;assert value>=0;length+=1
        assert value==0 and length%2==0;lengths.append(length)
    # This assertion is the proved consequence, not an assumed input frame.
    assert blocks%registers==0 and len(set(lengths))==1 and lengths[0]%2==0
    assert (q-1)%(W-1)==0
    completed=dict(z,Htime=(q-1)//(W-1))
    return safe.verify_decoded(completed,P,registers)


def canonical(x,controls,registers,variant=0):
    if registers==1:return single.canonical(x,tuple(row[0] for row in controls),variant)
    z,P=safe.canonical(x,controls,registers,variant);del z['Htime']
    verify_outer(z,registers);verify_decoded(z,P,registers);return z,P


def partial_counterexample(kind):
    k=3;blocks=4
    if kind=='non_even_initial_registers':
        R=9;values=[0,1,1,1];signs=[1,-1,-1,-1];I=R+R*R;F=0
        initial=[0,1,1];final_by_counter=[0,0,0]
    else:
        assert kind=='nonzero_final_registers'
        R=27;values=[2,0,0,3];signs=[1,1,1,-1];I=2;F=1+R+2*R*R
        initial=[2,0,0];final_by_counter=[2,1,1]
    W=R**k;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1);T=(R//3)*H
    A0=A1=Kp=Km=0
    for b,(a,epsilon) in enumerate(zip(values,signs)):
        f,s=single.split_ternary(a,b);A0+=f*R**b;A1+=s*R**b
        if epsilon==1:Kp+=R**b
        else:Km+=R**b
    z=dict(x=I//2,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
           F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
           alpha=q+J-(2*J+A0+A1),alphaI=(W if kind=='non_even_initial_registers' else R)-I)
    assert min(z.values())>0 and I%2==0
    assert H*(R-1)==q-1 and q==W*z['v'] and blocks%k!=0
    assert (q-1)%(W-1)!=0
    A=A0+A1;delta=Kp-Km
    assert I+(W-1)*A+W*delta==q*F
    assert z['FKplus']+z['FKminus']==2*J+H==3*T
    assert z['F0']+z['F1']+z['alpha']==q+J
    P=single.packed(z);ell=power_log(q,3);scale=q**6
    assert all(native(z[n],ell) and z[n]<q for n in single.FIELDS)
    assert native(P,6*ell) and P%3==2 and P%2==0
    assert central_valuation(P)==6*ell and P>q**5 and 2*P<3*(scale-1)
    assert scale>=81 and P>=27 and P<2*scale and scale<P*P
    return dict(kind=kind,registers=k,counter_blocks=blocks,counter_lengths=[2,1,1],outer=z,
                raw_input=I,raw_output_word=F,initial_registers=initial,final_registers=final_by_counter,
                source_block_values=values,controls=signs,packed=P,scale=scale,valuation=6*ell,
                changed_condition=('Input bound weakened from2x<R to2x<W, allowing odd higher initial registers.'
                                   if kind=='non_even_initial_registers' else
                                   'Zero target replaced by qF; the final output word starts at the partial-frame boundary and is cyclically rotated.'),
                positive_pell_extension='The word is native unit-two and even, the scale is a power of3, and all general-scale inequalities hold. The plus43 positive converse supplies every Pell auxiliary.')


def verify_regression(registers):
    phase_cases=partial=0
    for k in range(2,13):
        for blocks in range(k,201):
            lengths=[len(range(i,blocks,k)) for i in range(k)]
            assert all(n>=1 for n in lengths)
            assert all(n%2==0 for n in lengths)==(blocks%k==0 and (blocks//k)%2==0)
            phase_cases+=1;partial+=blocks%k!=0
    cases=0;samples=[]
    if registers==1:
        for x in range(1,16):
            controls=[(e,) for e in (1,-1)+(-1,)*(2*x)]
            z,P=canonical(x,controls,1);verify_decoded(z,P,1);cases+=1
            if len(samples)<2:samples.append(dict(outer=z,packed=P))
    else:
        for height in (4,6):
            first=safe.admissible_signs(2,height,True);others=safe.admissible_signs(0,height)
            for words in product(first,*([others]*(registers-1))):
                z,P=canonical(1,list(zip(*words)),registers);cases+=1
                if len(samples)<2:samples.append(dict(outer=z,packed=P,meaning=verify_decoded(z,P,registers)))
    return dict(registers=registers,chain_length_cases=phase_cases,rejected_partial_length_patterns=partial,
                complete_canonical_cases=cases,samples=samples,
                scope='Exact length-parity classification for2..12registers and up to200blocks; canonical zero-target histories. No controller or huge Pell witnesses are tested.')


def verify():
    return dict(status='PASS_PARITY_ALIGNED_FACTORED_RAW_COUNTERS',
                variants=[dict(arithmetic=verify_certificate(k),regression=verify_regression(k)) for k in (1,2,3)],
                counterexamples=[partial_counterexample(kind) for kind in ('non_even_initial_registers','nonzero_final_registers')],
                proof='../1980/EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md',
                scope='Exact76/77/78 first-plus rawregister zero-target components; completeframes are derived only for the specified eveninitial/allzeroend interface. Not universal certificates.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for row in result['variants']:
        print(row['arithmetic']['registers'],row['arithmetic']['operations'],row['arithmetic']['primitive_histogram'])
        print({k:v for k,v in row['regression'].items() if k not in ('samples','scope')})
