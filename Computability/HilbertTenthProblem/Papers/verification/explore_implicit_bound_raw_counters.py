#!/usr/bin/env python3
"""Remove the derived aggregate bound from raw-counter components:74/75/76."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_parity_aligned_raw_counters as old
from explore_native_ternary_ripple import native, central_valuation
from explore_native_ternary_history import power_log


REMOVED_INSTRUCTIONS={'bound_rhs','bound_lhs'}


def symbols(registers):
    z,outer=old.symbols(registers)
    return {n:v for n,v in z.items() if n!='alpha'},[n for n in outer if n!='alpha']


def schedule(registers):
    return [row for row in old.schedule(registers) if row[0] not in REMOVED_INSTRUCTIONS]


def equalities(registers):
    return [p for i,p in enumerate(old.equalities(registers)) if i!=5]


def source_residuals(registers):
    return [p for i,p in enumerate(old.source_residuals(registers)) if i!=5]


def verify_certificate(registers):
    z,outer=symbols(registers);env=dict(z)
    instructions=schedule(registers);hist=old.baseline.run_schedule(instructions,env)
    pairs=equalities(registers);source=source_residuals(registers);records=[]
    u=z['j']*z['c']+2*z['r']+1
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[17]*(u*u-z['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,(registers,i)
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(sp.expand(p)),
                            actual=sp.sstr(actual),correction=sp.sstr(sp.expand(extra))))
    primitive,counts=old.verify_primitives(instructions,env)
    assert len(primitive)==73+registers and counts=={'+':37,'*':36+registers}
    assert len(source)==len(pairs)==(20 if registers==1 else 21)
    assert len(outer+old.single.CORE_NAMES)==(30 if registers==1 else 31)
    assert all(p.free_symbols<=set(z.values()) for p in source)
    used={v for row in instructions for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(z)<=used and 'alpha' not in used
    assert not any(row[0] in REMOVED_INSTRUCTIONS for row in instructions)
    assert all(new==prior for new,prior in zip(source,
               [p for i,p in enumerate(old.source_residuals(registers)) if i!=5]))
    return dict(status='PASS',registers=registers,operations=len(primitive),
                primitive_histogram=counts,histogram=hist,parameters=['x'],
                positive_unknowns=outer+old.single.CORE_NAMES,unknown_count=len(outer+old.single.CORE_NAMES),
                equations=len(source),primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_positive_unknown='alpha',deleted_source_index=5,
                                 deleted_primitive_registers=sorted(REMOVED_INSTRUCTIONS),
                                 all_retained_source_polynomials='identical to the frozen predecessor'))


def verify_outer(z,registers):
    q,J,W,H,T=[z[n] for n in ['q','Jrep','W','H','T']]
    R=z['R'] if registers>1 else W
    assert min(z.values())>0 and 'alpha' not in z
    assert q==2*J+1 and q==W*z['v'] and W==R**registers
    assert H*(R-1)==2*J and 2*z['x']+z['alphaI']==R
    assert z['FKplus']+z['FKminus']==2*J+H==3*T
    assert z['G0']==z['F0']+T and z['G1']==z['F1']+T
    S=z['F0']+z['F1'];A=S-2*J;delta=z['FKplus']-z['FKminus']
    assert W*(A+delta)==A-2*z['x']
    # Derived before invoking any ternary or Pell statement.
    assert R>=3 and W%2==1 and H%2==0 and H>=2 and q//R>=3
    assert q>=9 and J>=4 and H<=J and T<=J
    assert 2*S<=13*J-8
    assert 2*max(z['F0'],z['F1'])<=13*J-10
    assert 2*max(z['G0'],z['G1'])<=15*J-10
    P=old.single.packed(z);D0=q**6
    assert q**5<P<2*D0 and D0>=81 and P>=27 and D0<P*P
    return P


def normalized_chunks(z):
    q=z['q'];carry=0;digits=[];carries=[0]
    for name in old.single.FIELDS:
        carry,digit=divmod(z[name]+carry,q)
        digits.append(digit);carries.append(carry)
    return digits,carries


def verify_accepting(z,P,registers):
    q=z['q'];J=z['Jrep'];ell=power_log(q,3)
    assert ell and ell>=2 and central_valuation(P)>=6*ell
    # These assertions are the independently proved overflow/carry consequences.
    assert P<q**6 and native(P,6*ell) and P%3==2
    chunks,carries=normalized_chunks(z)
    assert all(native(p,ell) for p in chunks) and carries[-1]==0
    a=z['F0']//q;b=z['F1']//q
    assert 0<=a<=3 and 0<=b<=3 and carries[1]==0
    assert carries[2]==a and carries[3]==a
    epsilon=carries[4]-b
    assert epsilon in (0,1) and carries[5]==b
    u=chunks[2]-J;v=chunks[4]-J
    A=z['F0']+z['F1']-2*J
    assert A==(a+b)*(q-1)+u+v-epsilon
    assert 4*A<3*(q-1)
    assert a==b==epsilon==0 and all(c==0 for c in carries)
    assert all(z[n]==p and native(z[n],ell) for n,p in zip(old.single.FIELDS,chunks))
    assert A<=J
    restored=dict(z,alpha=q+J-z['F0']-z['F1'])
    assert restored['alpha']>=1
    # Reuse only after restoring the deleted positive source witness.
    old.verify_outer(restored,registers)
    meaning=old.verify_decoded(restored,P,registers)
    return meaning,restored['alpha']


def canonical(x,controls,registers,variant=0):
    z,P=old.canonical(x,controls,registers,variant);del z['alpha']
    assert verify_outer(z,registers)==P
    meaning,alpha=verify_accepting(z,P,registers)
    z_with_index=dict(z,r=P)
    source=source_residuals(registers);sym,_=symbols(registers)
    sub={sym[n]:value for n,value in z_with_index.items()}
    outer_indices=list(range(10))+([20] if registers>1 else [])
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in outer_indices)
    return z,P,meaning,alpha


def verify_preliminary_and_masks(registers):
    pre=over_old_bound=power_cases=accepted=0;samples=[]
    # Complete positive splits in this finite geometry range, with no alpha filter.
    for q in range(3,100,2):
        J=(q-1)//2
        for R in range(3,q+1,2):
            W=R**registers
            if W>q or q%W or (q-1)%(R-1):continue
            H=(q-1)//(R-1);head=2*J+H
            if head%3:continue
            T=head//3
            for kp in range(1,head):
                km=head-kp;delta=kp-km
                for I in range(2,R,2):
                    numerator=-W*delta-I
                    if numerator%(W-1):continue
                    S=numerator//(W-1)+2*J
                    for f0 in range(1,S):
                        f1=S-f0
                        z=dict(x=I//2,q=q,Jrep=J,W=W,H=H,v=q//W,T=T,
                               F0=f0,F1=f1,G0=f0+T,G1=f1+T,FKplus=kp,FKminus=km,alphaI=R-I)
                        if registers>1:z['R']=R
                        P=verify_outer(z,registers);pre+=1;over_old_bound+=S>3*J
                        ell=power_log(q,3)
                        if not ell:continue
                        power_cases+=1
                        if central_valuation(P)<6*ell:continue
                        meaning,alpha=verify_accepting(z,P,registers);accepted+=1
                        if len(samples)<2:samples.append(dict(outer=z,packed=P,restored_alpha=alpha,meaning=meaning))
    return dict(prepower_positive_tuples=pre,tuples_above_deleted_bound=over_old_bound,
                power_scale_tuples=power_cases,complete_mask_acceptances=accepted,samples=samples,
                scope='All retained positive outer tuples in odd q<100, all possible register radices, flags, even raw inputs and track splits; no deleted-bound or native-field filter.')


def verify_canonical(registers):
    cases=0;samples=[]
    if registers==1:
        for x in range(1,16):
            controls=[(e,) for e in (1,-1)+(-1,)*(2*x)]
            z,P,meaning,alpha=canonical(x,controls,1);cases+=1
            if len(samples)<2:samples.append(dict(outer=z,packed=P,meaning=meaning,restored_alpha=alpha))
    else:
        for height in (4,6):
            first=old.safe.admissible_signs(2,height,True)
            others=old.safe.admissible_signs(0,height)
            for words in product(first,*([others]*(registers-1))):
                z,P,meaning,alpha=canonical(1,list(zip(*words)),registers);cases+=1
                if len(samples)<2:samples.append(dict(outer=z,packed=P,meaning=meaning,restored_alpha=alpha))
    return dict(complete_canonical_cases=cases,samples=samples,
                scope='Complete source and mask checks with unique deleted-alpha restoration; every other positive witness is unchanged. Enormous Pell witnesses follow from the frozen converse.')


def verify():
    return dict(status='PASS_IMPLICIT_BOUND_RAW_COUNTERS_74_75_76',
                variants=[dict(arithmetic=verify_certificate(k),
                               finite_outer_and_masks=verify_preliminary_and_masks(k),
                               canonical=verify_canonical(k)) for k in (1,2,3)],
                proof='../1980/EXPLORATION_IMPLICIT_BOUND_RAW_COUNTERS.md',
                overflow_proof='../1980/EXPLORATION_RAW_ALPHA_OVERFLOW_LEMMA.md',
                scope='Exact first-plus raw numerical zero-target components. The removed aggregate bound is derived by the full range, overflow and field-carry proofs. No universal-machine certificate is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for row in result['variants']:
        print(row['arithmetic']['registers'],row['arithmetic']['operations'],row['arithmetic']['primitive_histogram'])
        print({k:v for k,v in row['finite_outer_and_masks'].items() if k not in ('samples','scope')})
        print(row['canonical']['complete_canonical_cases'])
