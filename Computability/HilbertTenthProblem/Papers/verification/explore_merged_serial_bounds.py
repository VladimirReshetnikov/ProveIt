#!/usr/bin/env python3
"""Exact119 serial composition: shared positive bound and NC reuse."""
from pathlib import Path
import json
import sympy as sp
import explore_implicit_bound_serial_composition as old
from explore_native_ternary_ripple import native,central_valuation


PROGRAM=dict(old.old.PROGRAM)
ZALL=PROGRAM['Zc']+PROGRAM['hs']+PROGRAM['hz']
M=PROGRAM['K']*PROGRAM['S']+ZALL
assert ZALL>PROGRAM['S']
while PROGRAM['Rmin']<=12*(M+1):
    PROGRAM['Rmin']*=9;PROGRAM['B']+=2
assert PROGRAM['Rmin']%old.old.PROGRAM['Rmin']==0
OUTER_NAMES=[name for name in old.OUTER_NAMES if name not in ('alphaT','alphaP')]+['beta']
CORE_NAMES=old.old.CORE_NAMES
SYM={name:sp.Symbol(name) for name in ['x']+OUTER_NAMES+CORE_NAMES}
FIELDS=old.old.FIELDS


def build():
    prior_ops,prior_pairs,prior_source=old.build()
    ops=[]
    for name,op,left,right in prior_ops:
        if name in ('twice_T','top_bound','program_native_C'):continue
        if name=='top_mask':left,right=6,'T'
        if name=='program_bound':
            ops.append(('combined_sum','+','program_bound_sum','T'))
            left,right='combined_sum','beta'
        if name=='program_R_bound':left=PROGRAM['Rmin']
        ops.append((name,op,left,right))
    pairs=[];source=[];origins=[]
    for i,(pair,poly) in enumerate(zip(prior_pairs,prior_source)):
        if i==21:continue
        if i==25:poly=SYM['T']+SYM['PTC']+SYM['PTV']+SYM['beta']-SYM['q']
        if i==26:pair=('PNC','program_C_lhs')
        if i==30:poly=SYM['R']-PROGRAM['Rmin']*SYM['zR']
        pairs.append(pair);source.append(poly);origins.append(i)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    hist=old.old.aligned.baseline.run_schedule(ops,env);records=[]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for i,((left,right),p,prior_index) in enumerate(zip(pairs,source,origins)):
        actual=sp.expand(env[left]-env[right])
        extra=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,i
        if prior_index not in (25,30):assert p==old.build()[2][prior_index]
        records.append(dict(index=i,prior_index=prior_index,equality=[left,right],
                            source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=old.old.aligned.verify_primitives(ops,env)
    assert len(primitive)==119 and counts=={'+':63,'*':56}
    assert len(source)==len(pairs)==31 and len(OUTER_NAMES+CORE_NAMES)==43
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    used={v for row in ops for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used
    assert not (used&{'alphaT','alphaP','twice_T','program_native_C'})
    return dict(status='PASS',operations=119,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=43,
                equations=31,primitive_instructions=primitive,equalities=pairs,residuals=records,
                fixed_program=PROGRAM,
                exact_delta=dict(removed_unknowns=['alphaT','alphaP'],new_unknown='beta',
                    merged_equation='T+PTC+PTV+beta=q',native_C_reuse='PNC=program_C_lhs',
                    old_threshold_multiplier=PROGRAM['Rmin']//old.old.PROGRAM['Rmin']))


def bounds_regression():
    merged=margin_cases=last_block_cases=0
    for q in range(9,66,2):
        J=(q-1)//2
        for H in range(1,min(J,6)+1):
            for difference in range(1,4):
                for C in range(1,7):
                    for V in range(1,7):
                        TC=C+J-H;TV=V+(1+difference)*H
                        total=TC+TV
                        assert total==J+C+V+difference*H and TC>0 and TV>0
                        for T in range(1,q-total):
                            beta=q-T-total
                            assert beta>0 and T<=J and q-2*T>0 and q-total>0
                            merged+=1
    for bound in range(1,101):
        R=9
        while R<=12*(bound+1):R*=3
        for blocks in range(1,7):
            q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
            Tmax=q//3+(q//R-1)//2
            assert 2*Tmax==2*q//3+q//R-1
            assert q-Tmax-J-bound*H>0
            assert sp.Rational(1,3)+sp.Rational(1,2*R)+sp.Rational(1,2)+sp.Rational(bound,R-1)<sp.Rational(35,36)
            margin_cases+=1
    # Every possible zero-event head set with its last bit zero is checked.
    for R in (9,27,81):
        for blocks in range(1,9):
            q=R**blocks;H=(q-1)//(R-1)
            for mask in range(1<<(blocks-1)):
                Z=sum(((mask>>b)&1)*R**b for b in range(blocks-1))
                T=(R//3)*H+((R-3)//6)*Z
                assert T<=q//3+(q//R-1)//2
                last_block_cases+=1
    return dict(positive_merged_bound_tuples=merged,strict_frame_margin_cases=margin_cases,
                last_zero_flag_absent_cases=last_block_cases,
                scope='Finite positive source tuples test old-bound restoration without native assumptions; scalar widths test the general margin; exhaustive short zero-head sets test the last-block estimate.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0];blocks=len(path)-1
    R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0;zero_events=0;last_source=None
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0;zero_events+=1
        a,d=old.old.aligned.single.split_ternary(n,b);weight=R**b
        A0+=a*weight;A1+=d*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight
        last_source=(n,c['signs'][state],c['zeros'][state])
        values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and blocks%6==0 and last_source==(1,-1,0)
    T=(R//3)*H+((R-3)//6)*Z
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*Z
    TC=C+J-c['S']*H;TV=V+ZALL*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
        F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
        FZ=J+Z,FZbar=J+H-Z,alphaI=R-2*x,PC=C,PV=V,PTC=TC,PTV=TV,
        beta=q-T-TC-TV,PNC=J+C,PNV=J+V,PNTC=J+TC,PNTV=J+TV,zR=1)
    assert min(z.values())>0 and 2*T<q and TC+TV<q
    assert TC+TV==J+C+V+(ZALL-c['S'])*H>J
    assert T<=q//3+(q//R-1)//2 and TC<=J and TV<M*H
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));z['r']=P
    ops,pairs,source,origins=build()
    indices=[i for i,prior in enumerate(origins) if prior<10 or prior>=20]
    sub={SYM[n]:value for n,value in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(z[n],ell) and z[n]<q for n in FIELDS)
    assert native(P,12*ell) and P%3==2 and P%2==0 and P<q**12
    assert central_valuation(P)==12*ell and q**12<P*P
    # Restored old slacks and quotient, with every other supplied value fixed.
    restored=dict(z,alphaT=q-2*T,alphaP=q-TC-TV,
                  zR=R//old.old.PROGRAM['Rmin'])
    restored.pop('beta')
    old_source=old.build()[2]
    old_sub={old.SYM[n]:value for n,value in restored.items()}
    old_indices=list(range(10))+list(range(20,len(old_source)))
    assert min(restored.values())>0
    assert all(old_source[i].subs(old_sub,simultaneous=True)==0 for i in old_indices)
    return dict(x=x,path=path,block_steps=blocks,bank_rounds=blocks//3,counter_width=c['B'],
                zero_event_count=zero_events,last_source=list(last_source),outer_residuals=len(indices),
                restored_old_outer_residuals=len(old_indices),packed_bits=P.bit_length(),valuation=12*ell,
                positive_beta=True,positive_old_slacks=True,
                full_positive_extension='All twelve fields are native; packed index is even and unit-two; original complete fixed-sign43 positive converse applies. Huge Pell coordinates are not instantiated.')


def verify():
    return dict(status='PASS_MERGED_SERIAL_BOUNDS_119',arithmetic=verify_certificate(),
                bounds=bounds_regression(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_MERGED_SERIAL_BOUNDS.md',
                scope='Complete serial labelled rawcounter relation preserved with wider fixed threshold. Not a same-width witness bijection or a new universal-machine compiler.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['bounds']);print(result['canonical'])
