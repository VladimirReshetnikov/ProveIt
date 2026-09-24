#!/usr/bin/env python3
"""Exact116: recover T's bound through the two typed zero flags."""
from pathlib import Path
import json
import sympy as sp
import explore_complement_zero_serial_composition as old
from explore_native_ternary_ripple import native,central_valuation


SYM=old.SYM
OUTER_NAMES=old.OUTER_NAMES
CORE_NAMES=old.CORE_NAMES
PROGRAM=old.PROGRAM
FIELDS=old.FIELDS


def build():
    prior_ops,pairs,prior_source=old.build();ops=[]
    for name,op,left,right in prior_ops:
        if name=='combined_sum':continue
        if name=='program_bound':left='program_bound_sum'
        ops.append((name,op,left,right))
    source=list(prior_source)
    source[24]=SYM['PTC']+SYM['PTV']+SYM['beta']-SYM['q']
    return ops,pairs,source


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM)
    hist=old.old.old.old.old.aligned.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitive)==116 and counts=={'+':60,'*':56}
    assert len(source)==len(pairs)==31 and len(OUTER_NAMES+CORE_NAMES)==43
    prior=old.build()[2];z=SYM
    assert sp.expand(source[24]-prior[24].subs(z['beta'],z['beta']-z['T']))==0
    u=z['j']*z['c']+2*z['r']+1;records=[]
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[17]*(u*u-z['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,i
        if i!=24:assert p==prior[i]
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    used={v for row in ops for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used and 'combined_sum' not in used
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=116,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=43,
                equations=31,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_register='combined_sum',new_bound='PTC+PTV+beta=q',
                    positive_witness_maps='beta_new=beta_old+T; beta_old=beta_new-T is positive after decoded last-source/width bounds',
                    unchanged_source_count=30))


def verify_symbolic_bounds():
    q,R,t=sp.symbols('q R t');J=(q-1)/2
    guard_gap=sp.factor(q*q-(4*q+(q+3)*q/12))
    low_upper=sp.Rational(3,2)*q**6+5*q**5+5*q**3+sp.Rational(3,2)*q
    low_gap=sp.expand(2*(2*q**6-low_upper))
    full_upper=2*q**6+(3*J-1)*q**6*sum(q**i for i in range(6))
    full_gap=sp.factor(sp.Rational(3,2)*(q**12-1)-full_upper)
    full_numerator=sp.expand(2*(q-1)*full_gap)
    post_guard_gap=sp.factor(R*q-(3*J+(R+3)*J/6+1))
    assert sp.expand(post_guard_gap-((11*R-21)*q+R+9)/12)==0
    assert sp.expand(full_numerator-(2*q**12-(q+1)*q**6-3*q+3))==0
    polynomials=[(12*guard_gap,9),(low_gap,27),(full_numerator,9)]
    margins=[]
    for polynomial,minimum in polynomials:
        coeff=sp.Poly(sp.expand(polynomial.subs(q,t+minimum)),t).all_coeffs()
        assert all(c>0 for c in coeff)
        margins.append(dict(polynomial=sp.sstr(sp.expand(polynomial)),minimum_q=minimum,
                            shifted_positive_coefficients=list(map(str,coeff))))
    return dict(positive_margins=margins,post_guard_gap=sp.sstr(post_guard_gap),
                scope='Exact pre-mask low/full packing gaps and post-first-sign guard inequality; q initially ranges over integers, not just powers of3.')


def selected(values):
    values=sorted(set(values))
    if len(values)<=9:return values
    return [values[i] for i in sorted({0,1,2,len(values)//2,len(values)-3,len(values)-2,len(values)-1})]


def verify_finite_bootstrap():
    pre=large_T=whole_native=post_first=zero_recovered=0;samples=[]
    staged_first=staged_large_T=staged_zero=0
    for R,blocks in ((9,4),(9,6),(27,4),(27,6),(81,4)):
        q=R**blocks;W=R**3;J=(q-1)//2;H=(q-1)//(R-1);head=2*J+H
        ell=old.round_log(R)*blocks
        for I in selected(range(2,R,2)):
            step=(W-1)//2;residue=((head-I)//2)%step
            candidates=selected(range(residue or step,head,step))
            # Two bank rounds: counter0 decrements twice; the other two
            # counters execute plus,minus. This contributes a native first
            # chunk even when the coarse endpoint sampler misses all of them.
            if blocks==6 and I==2:candidates=sorted(set(candidates+[J+R+R*R]))
            for kp in candidates:
                km=head-kp;delta=kp-km;numerator=-W*delta-I
                assert numerator%(W-1)==0
                A=numerator//(W-1);S=A+2*J
                if S<2:continue
                for f0 in selected(v for v in (1,2,J-1,J,J+1,q-1,q,q+1,S//2,S-2,S-1) if 0<v<S):
                    f1=S-f0
                    for fd in selected(v for v in (1,2,J-R,J-2,J-1,J,J+1,J+R,head-2,head-1) if 0<v<head):
                        numerator_T=6*J-(R-3)*(fd-J)
                        assert numerator_T%6==0;T=numerator_T//6
                        if T<=0:continue
                        fz=head-fd;g0=f0+T;g1=f1+T
                        fields=[kp,g0,f0,g1,f1,km,fz,fd,J+1,J+1,J+1,J+1]
                        assert 2*S<=13*J-8 and f0<4*q and f1<4*q
                        assert 6*T<(R+3)*J and max(g0,g1)<q*q
                        P6=sum(v*q**i for i,v in enumerate(fields[:6]))
                        P=sum(v*q**i for i,v in enumerate(fields))
                        assert q**5<P6<2*q**6 and q**11<P and 2*P<3*(q**12-1)
                        pre+=1;large_T+=T>J
                        carry=0;chunks=[];carries=[0]
                        for field in fields:
                            carry,digit=divmod(field+carry,q);chunks.append(digit);carries.append(carry)
                        # These are strictly weaker acceptance filters than the
                        # whole-word mask, and exercise the new bootstrap stages.
                        if native(chunks[0],ell):
                            staged_first+=1;staged_large_T+=T>J
                            assert carries[1]==0 and kp>=J and 32*A<9*J and max(f0,f1)<3*J
                            assert max(g0,g1)+1<R*q
                            assert carries[2]<=R-1 and carries[3]<=1 and carries[4]<=R-1 and carries[5]<=1
                            assert km+carries[5]<q and carries[6]==0
                            if native(chunks[6],ell) and native(chunks[7],ell):
                                staged_zero+=1
                                assert carries[7]==carries[8]==0 and fz>=J and J<=fd<q and T<=J
                        # The conditional carry proof starts with the whole native word.
                        if not (P<q**12 and P%3==2 and native(P,12*ell)):continue
                        whole_native+=1
                        assert all(native(chunk,ell) for chunk in chunks)
                        assert carries[1]==0 and kp>=J and 32*A<9*J and max(f0,f1)<3*J
                        post_first+=1
                        assert max(g0,g1)+1<R*q
                        assert carries[2]<=R-1 and carries[3]<=1 and carries[4]<=R-1 and carries[5]<=1
                        assert km+carries[5]<q and carries[6]==0
                        assert carries[7]==0 and fz>=J and fd<q and fd>=J and carries[8]==0
                        assert T<=J;zero_recovered+=1
                        assert all(c==0 for c in carries)
                        if len(samples)<4:samples.append(dict(R=R,blocks=blocks,I=I,fields=fields,T=T,packed=P))
    assert staged_first>0 and staged_large_T>0 and staged_zero>0
    return dict(retained_preliminary_tuples=pre,tuples_with_T_above_J=large_T,
                first_native_chunk_cases=staged_first,first_native_chunk_with_T_above_J=staged_large_T,
                first_and_both_zero_chunks_native_cases=staged_zero,
                native_whole_word_candidates=whole_native,post_first_sign_cases=post_first,
                zero_pair_recovered_cases=zero_recovered,samples=samples,
                scope='Selected exact numerical time/flag/top-source tuples in five power geometries, including T>J. The four program chunks are arbitrary fixed native placeholders; no full controller or accepting-path claim is made for this finite lemma check.')


def verify_native_prefixes():
    """Small exact raw histories; program chunks are explicitly placeholders."""
    split=old.old.old.old.old.aligned.single.split_ternary
    cases=zero_events=0;samples=[]
    for x in range(1,4):
        for R in (27,81):
            controls=[(1,1,1),(-1,-1,-1)]
            controls += [(-1,1 if i%2==0 else -1,1 if i%2==0 else -1) for i in range(2*x)]
            blocks=3*len(controls);q=R**blocks;W=R**3;J=(q-1)//2;H=(q-1)//(R-1)
            ell=old.round_log(R)*blocks
            for variant in range(3):
                for zero_mode in range(3):
                    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
                    for b,epsilon in enumerate(e for row in controls for e in row):
                        lane=b%3;n=values[lane];assert 0<=n<R//3
                        a0,a1=split(n,b+variant);weight=R**b
                        A0+=a0*weight;A1+=a1*weight
                        if epsilon==1:Kp+=weight
                        else:Km+=weight
                        if n==0 and (zero_mode==1 or zero_mode==2 and b%2==0):
                            Z+=weight;zero_events+=1
                        values[lane]+=epsilon;assert min(values)>=0
                    assert values==[0,0,0] and Kp+Km==H
                    D=H-Z;T=(R//3)*H+((R-3)//6)*Z
                    A=A0+A1;delta=Kp-Km
                    assert W*(A+delta)==A-2*x and 6*(J-T)==(R-3)*D
                    f0,f1=J+A0,J+A1
                    fields=[J+Kp,f0+T,f0,f1+T,f1,J+Km,J+Z,J+D]+[J+1]*4
                    P=sum(f*q**i for i,f in enumerate(fields))
                    assert all(0<f<q and native(f,ell) for f in fields)
                    assert P%3==2 and P%2==0 and native(P,12*ell) and P<q**12
                    assert central_valuation(P)==12*ell and q**12<P*P
                    assert 32*A<9*J and max(f0,f1)<3*J
                    carry=0;carries=[0]
                    for field in fields:carry,_=divmod(field+carry,q);carries.append(carry)
                    assert max(carries)==0 and T<=J
                    cases+=1
                    if len(samples)<3:samples.append(dict(x=x,R=R,blocks=blocks,split_variant=variant,
                        zero_mode=zero_mode,packed_bits=P.bit_length(),valuation=12*ell))
    assert cases==54 and zero_events>0
    return dict(native_whole_word_prefix_cases=cases,source_zero_events=zero_events,samples=samples,
        scope='Fresh exact three-counter paths with three digit-split variants, all/no/selective legal zero requests, four native placeholder program chunks, every new carry stage and exact central valuation. These are raw/zero-interface tests, not complete ROM solutions; full117 canonical receipts are inherited separately.')


def inherited_canonical_receipt():
    path=Path(old.__file__).with_suffix('.json')
    receipt=json.loads(path.read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_COMPLEMENT_ZERO_SERIAL_COMPOSITION_117'
    assert receipt['arithmetic']['operations']==117
    rows=[]
    for row in receipt['canonical']:
        assert row['positive_beta'] and row['outer_residuals']==21
        rows.append(dict(**row,evidence='Inherited frozen117 canonical receipt; no rerun of unchanged packed/Pell data.',
                         source_transport='Every new residual vanishes after beta_new=beta_old+T; this identity is freshly checked for all symbolic coordinates.'))
    return rows


def verify():
    return dict(status='PASS_PROGRAM_ONLY_SERIAL_BOUND_116',arithmetic=verify_certificate(),
                symbolic_bounds=verify_symbolic_bounds(),finite_bootstrap=verify_finite_bootstrap(),
                native_prefix_regression=verify_native_prefixes(),
                inherited_117_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_PROGRAM_ONLY_SERIAL_BOUND.md',
                scope='Complete116-operation universal family by an exact positive beta reparameterization. New source/bound/carry evidence is fresh; unchanged full canonical receipts are explicitly inherited. Universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['finite_bootstrap'].items() if k not in ('samples','scope')})
