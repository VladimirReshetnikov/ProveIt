#!/usr/bin/env python3
"""Exact104: complement both conceptual counter guard fields."""
from pathlib import Path
import json
import sympy as sp
import explore_factored_raw_blocks as old
from explore_native_ternary_ripple import native,central_valuation

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=['Tgap' if name=='T' else name for name in old.OUTER_NAMES]
SYM={name:symbol for name,symbol in old.SYM.items() if name!='T'}
SYM['Tgap']=sp.Symbol('Tgap',integer=True,positive=True)
FIELDS=old.FIELDS


def conceptual_fields():
    return dict(Kp=SYM['Kp'],B0=SYM['Tgap']-SYM['A0'],A0=SYM['A0'],
                B1=SYM['Tgap']-SYM['A1'],A1=SYM['A1'],Km=SYM['Km'],Z=SYM['Z'],
                Dzero=SYM['Dzero'],PC=SYM['PC'],PV=SYM['PV'],
                PTC=SYM['PC']+SYM['Jrep']-PROGRAM['S']*SYM['H'],
                PTV=SYM['PV']+ZALL*SYM['H'])


def build():
    prior,pairs,source,origins=old.build();ops=[]
    for name,op,left,right in prior:
        if name in ('top_complement','q_plus_one'):continue
        if name=='top_mask':right='Tgap'
        if name=='guard_A_scaled':left='twice_J'
        if name=='guard_T_scaled':right='Tgap'
        ops.append((name,op,left,right))
    source=[sp.expand(p.subs(old.SYM['T'],SYM['Jrep']-SYM['Tgap'])) for p in source]
    q=SYM['q'];raw=sum(conceptual_fields()[name]*q**i for i,name in enumerate(FIELDS))
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-q**12-2*raw)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==104 and counts=={'+':49,'*':55}
    assert len(source)==len(pairs)==22 and len(OUTER_NAMES+CORE_NAMES)==34
    q=SYM['q'];J=SYM['Jrep'];u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    raw=sum(conceptual_fields()[name]*q**i for i,name in enumerate(FIELDS))
    # q-1 is reused as twice_J. This one geometry correction is essential:
    # the packed arithmetic is the desired polynomial only modulo q=2J+1.
    pairA=SYM['A0']+q*q*SYM['A1']
    assert sp.expand(env['raw_packed']-raw+q*pairA*source[origins.index(0)])==0
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if origin==18 else 0
        if origin==9:correction=2*q*pairA*source[origins.index(0)]
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,(i,origin)
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'T','top_complement','q_plus_one'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=104,primitive_histogram=counts,parameters=['x'],
                positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=34,equations=22,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                retained_conceptual_masks=FIELDS,
                scope='Exact104 schedule/source. Counter guard masks are complemented, not omitted. Packed geometry correction is included; semantic sufficiency and changed-index necessity require the separate proof.')


def boolean(value,width):
    return value>=0 and native(value+(3**width-1)//2,width)


def verify_borrow_exclusion():
    cases=negative=accepted=0
    for width in range(1,6):
        q=3**width;J=(q-1)//2
        for gap in range(1,J//3+1):
            for A0 in range(1,J):
                for A1 in {1,J-A0}:
                    for kp in (1,J):
                        low=kp+q*(gap-A0)+q*q*A0+q**3*(gap-A1)+q**4*A1
                        assert low==kp+q*((q-1)*(A0+q*q*A1)+(q*q+1)*gap)
                        b0=gap-A0;b1=gap-A1
                        if b0<0:
                            assert low//q%q==q+b0>J
                            negative+=1
                        elif b1<0:
                            assert low//q**3%q==q+b1>J
                            negative+=1
                        if all(boolean(low//q**i%q,width) for i in range(5)):
                            assert b0>=0 and b1>=0
                            assert boolean(J-b0,width) and boolean(J-b1,width)
                            accepted+=1
                        cases+=1
    # Exhaust Boolean guard values, including zero placeholders and the
    # maximal old guard J whose new complement is zero.
    complements=zero=0
    for width in range(1,8):
        q=3**width;J=(q-1)//2
        words=[sum(((bits>>i)&1)*3**i for i in range(width)) for bits in range(1<<width)]
        for b0 in words:
            for b1 in words:
                assert boolean(J-b0,width) and boolean(J-b1,width)
                assert (J*(q+q**3)-2*(b0*q+b1*q**3))%2==0
                complements+=1;zero+=b0==J or b1==J
    return dict(signed_guard_windows=cases,negative_guard_windows_rejected=negative,
                accepted_signed_windows=accepted,exhaustive_complement_pairs=complements,
                pairs_including_zero_complement=zero,
                scope='General negative-field borrow obstruction and parity are proved separately; these are exhaustive bounded arithmetic checks, including zero raw complements.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
    aligned=old.old.old.ALIGNED
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        aa,bb=aligned.single.split_ternary(n,b);weight=R**b
        A0+=aa*weight;A1+=bb*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight;values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0]
    D=H-Z;gap=((R-3)//6)*D;T=J-gap
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    TC=C+J-c['S']*H;TV=V+ZALL*H;wide=(q**12-1)//2
    z=dict(x=x,q=q,Jrep=J,W=W,H=H,v=q//W,R=R,Tgap=gap,A0=A0,A1=A1,
           Kp=Kp,Km=Km,Z=Z,Dzero=D,alphaI=R-2*x,PC=C,PV=V)
    fields=[Kp,gap-A0,A0,gap-A1,A1,Km,Z,D,C,V,TC,TV]
    previous=[Kp,A0+T,A0,A1+T,A1,Km,Z,D,C,V,TC,TV]
    raw=sum(value*q**i for i,value in enumerate(fields));r=raw+wide
    oldraw=sum(value*q**i for i,value in enumerate(previous))
    z['r']=r;z['beta']=q**12-r
    assert min(z.values())>0 and min(fields)>=0
    assert raw-oldraw==J*(q+q**3)-2*((A0+T)*q+(A1+T)*q**3)
    assert (raw-oldraw)%2==0 and oldraw!=raw
    assert 0<3*gap<J and 0<A0+A1<J
    ops,pairs,source,origins=build();sub={SYM[name]:value for name,value in z.items()}
    indices=[i for i,origin in enumerate(origins) if origin<10 or origin>=20]
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(boolean(value,ell) for value in fields)
    assert native(r,12*ell) and r%3==2 and r%2==0 and q**11<r<q**12<r*r
    valuation=central_valuation(r);assert valuation==12*ell
    return dict(x=x,serial_blocks=blocks,counter_width=c['B'],outer_residuals=len(indices),
                positive_supplied_raw_fields=8,conceptual_masks=12,zero_conceptual_fields=sum(v==0 for v in fields),
                changed_packed_value=True,packed_bits=r.bit_length(),valuation=valuation,
                scope='Fresh changed-index complete outer tuple, all twelve Boolean masks, parity, unit-two condition and positive-kernel growth bounds. Huge Pell auxiliaries follow from the existing positive converse rather than numerical instantiation.')


def verify():
    return dict(status='PASS_COMPLEMENTED_COUNTER_GUARDS_104',arithmetic=verify_certificate(),
                borrowed_windows=verify_borrow_exclusion(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_COMPLEMENTED_COUNTER_GUARDS.md',
                scope='Complete104 universal construction with full independent proof/source reviews and fresh verification; this replaces two guard masks by their complements and changes the Pell index. Existing universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['borrowed_windows']);print(result['canonical'])
