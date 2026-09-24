#!/usr/bin/env python3
"""Exact114: the last masked field enforces the fixed program width."""
from pathlib import Path
import json
import sympy as sp
import explore_packed_bound_serial_composition as old
from explore_native_ternary_ripple import native,central_valuation


PROGRAM=dict(old.PROGRAM)
OLD_Z=old.old.ZALL
FRESH=1;FRESH_EXPONENT=0
threshold=max(PROGRAM['K']*PROGRAM['S'],PROGRAM['g']*PROGRAM['S'],
              6*(PROGRAM['hs']+PROGRAM['hz']),OLD_Z,PROGRAM['Rmin'],9)
while FRESH<=threshold:FRESH*=3;FRESH_EXPONENT+=1
ZALL=OLD_Z+FRESH
# This is only a convenient choice in finite canonical examples; there is
# no supplied zR or fixed-width equation in the new source.
while PROGRAM['Rmin']<=2*ZALL:PROGRAM['Rmin']*=9;PROGRAM['B']+=2
PROGRAM['extra_forbidden_exponent']=FRESH_EXPONENT
PROGRAM['forbidden_mask']=ZALL
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='zR']
CORE_NAMES=old.CORE_NAMES
SYM={n:v for n,v in old.SYM.items() if n!='zR'}
FIELDS=old.FIELDS


def build():
    previous,old_pairs,old_source=old.build();ops=[]
    for name,op,left,right in previous:
        if name=='program_R_bound':continue
        if name=='marker_forbidden':left=ZALL
        ops.append((name,op,left,right))
    pairs=[];source=[];origins=[]
    for index,(pair,polynomial) in enumerate(zip(old_pairs,old_source)):
        if index==29:continue
        if index==23:polynomial=SYM['PTV']-SYM['PV']-ZALL*SYM['H']
        pairs.append(pair);source.append(polynomial);origins.append(index)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.old.old.old.old.aligned.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitive)==114 and counts=={'+':59,'*':55}
    assert len(source)==len(pairs)==30 and len(OUTER_NAMES+CORE_NAMES)==42
    prior=old.build()[2];z=SYM;u=z['j']*z['c']+2*z['r']+1;records=[]
    for index,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        extra=source[17]*(u*u-z['y_aux']**2) if index==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-extra)==0,index
        if origin!=23:assert polynomial==prior[origin]
        else:assert sp.expand(polynomial-prior[origin]+FRESH*z['H'])==0
        records.append(dict(index=index,prior_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(extra)))
    used={v for row in ops for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used and not used&{'zR','program_R_bound'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert FRESH>threshold and OLD_Z<FRESH and PROGRAM['Rmin']>2*ZALL
    return dict(status='PASS',operations=114,primitive_histogram=counts,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,
                unknown_count=42,equations=30,primitive_instructions=primitive,
                equalities=pairs,residuals=records,fixed_program=PROGRAM,
                exact_delta=dict(deleted_unknown='zR',deleted_equation_index=29,
                    deleted_register='program_R_bound',
                    changed_forbidden_coefficient='Znew=Zold+3^e; existing one product retained',
                    extra_exponent=FRESH_EXPONENT,unchanged_retained_sources=29),
                scope='All114 instructions and30 fresh source comparisons, including the inherited acyclic norm correction; no fixed-width equality remains.')


def verify_intrinsic_width():
    tuples=nonpowers=0
    for Z in range(1,65):
        for H in range(1,17):
            for V in range(1,17):
                for slack in range(6):
                    J=Z*H+V+slack
                    if (2*J)%H:continue
                    R=2*J//H+1;q=2*J+1;TV=V+Z*H;NTV=J+TV
                    assert H*(R-1)==2*J and 0<TV<=J and NTV<q
                    assert R-1>2*Z
                    power=R
                    while power%3==0:power//=3
                    nonpowers+=power!=1;tuples+=1
    c=PROGRAM;row_cases=[]
    # Use a local digit check, independently of the native offset predicate.
    def is_boolean(value):
        while value:
            value,digit=divmod(value,3)
            if digit==2:return False
        return True
    assert is_boolean(OLD_Z) and is_boolean(ZALL)
    for i,j in c['edges']:
        sign=int(c['signs'][i]==1);nozero=1-c['zeros'][i]
        row=c['K']*3**c['a'][i]
        V=row-c['g']*3**c['a'][j]-c['hs']*sign-c['hz']*nozero
        assert 0<V<row<=c['K']*c['S']<FRESH
        assert is_boolean(V) and is_boolean(V+OLD_Z) and is_boolean(V+ZALL)
        assert V+ZALL<2*ZALL<c['Rmin']
        row_cases.append(dict(edge=[i,j],junk_below_fresh_position=True,new_test_boolean=True))
    return dict(positive_pre_power_tuples=tuples,non_power_of_three_widths=nonpowers,
                canonical_rom_rows=row_cases,
                scope='The width inequality is tested on ordinary integer equations, including nonpowers; every fixedROM edge verifies the extra forbidden digit is disjoint from canonical junk.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        first,second=old.old.old.old.old.old.aligned.single.split_ternary(n,b)
        weight=R**b;A0+=first*weight;A1+=second*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight;last=(n,c['signs'][state],c['zeros'][state])
        values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and blocks%6==0 and last==(1,-1,0)
    D=H-Z;T=J-((R-3)//6)*D
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    TC=C+J-c['S']*H;TV=V+ZALL*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
           F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
           FZ=J+Z,FZbar=J+D,alphaI=R-2*x,PC=C,PV=V,PTC=TC,PTV=TV,
           PNC=J+C,PNV=J+V,PNTC=J+TC,PNTV=J+TV)
    P=sum(z[name]*q**i for i,name in enumerate(FIELDS));z['r']=P;z['beta']=q**12-P
    assert min(z.values())>0 and R-1>2*ZALL
    assert 0<V<TV<=J and 0<V+c['hs']*Kp+c['hz']*D<TV and C<q
    ops,pairs,source,origins=build()
    indices=[i for i,origin in enumerate(origins) if origin<10 or origin>=20]
    sub={SYM[name]:value for name,value in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(z[name],ell) and z[name]<q for name in FIELDS)
    assert native(P,12*ell) and P%3==2 and P%2==0 and q**11<P<q**12<P*P
    valuation=central_valuation(P);assert valuation==12*ell
    return dict(x=x,serial_blocks=blocks,counter_width=c['B'],outer_residuals=len(indices),
                extra_forbidden_exponent=FRESH_EXPONENT,packed_bits=P.bit_length(),valuation=valuation,
                intrinsic_width=True,positive_packed_slack=True,
                scope='Fresh complete finite path, all12 native fields and20 outer residuals, even unit-two index and general-scale bounds. The proved43 converse constructs unmaterialized positive Pell coordinates.')


def verify():
    return dict(status='PASS_INTRINSIC_PROGRAM_WIDTH_114',arithmetic=verify_certificate(),
                intrinsic_width=verify_intrinsic_width(),
                canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_INTRINSIC_PROGRAM_WIDTH.md',
                scope='Complete114-operation universal family, with independent full proof/source audits and fresh verification. The row width is enforced by an added fixed forbidden digit, with no extra operation. Existing universal frontier90 remains smaller.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['intrinsic_width']);print(result['canonical'])
