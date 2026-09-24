#!/usr/bin/env python3
"""Exact110: one full-width offset for twelve positive raw fields."""
from pathlib import Path
import json
import sympy as sp
import explore_intrinsic_program_width as old
import explore_global_offset_positivity as positivity
from explore_native_ternary_ripple import native,central_valuation

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=['q','Jrep','W','H','v','T','A0','A1','B0','B1','Kp','Km','Z','Dzero',
             'alphaI','R','PC','PV','PTC','PTV','beta','Jwide']
SYM={n:sp.Symbol(n,integer=True,positive=True) for n in ['x']+OUTER_NAMES+CORE_NAMES}
FIELDS=['Kp','B0','A0','B1','A1','Km','Z','Dzero','PC','PV','PTC','PTV']
RAW_RENAMES=dict(FKplus='Kp',FKminus='Km',F0='A0',F1='A1',G0='B0',G1='B1',
                 FZ='Z',FZbar='Dzero',PNC='PC',PNV='PV',PNTC='PTC',PNTV='PTV')
base=old
while not hasattr(base,'aligned'):base=base.old
ALIGNED=base.aligned


def native_substitution():
    sub={s:SYM[name] for name,s in old.SYM.items() if name in SYM}
    sub.update({old.SYM[name]:SYM['Jrep']+SYM[raw] for name,raw in RAW_RENAMES.items()})
    return sub


def build():
    previous,oldpairs,oldsource,_=old.build()
    deleted={'head_rhs','raw_A','raw_D','raw_Kplus','program_native_V','program_native_TC','program_native_TV'}
    registers={'raw_A':'track_sum','raw_D':'Dzero','raw_Kplus':'Kp'}
    def rename(a):return RAW_RENAMES.get(a,registers.get(a,a))
    ops=[]
    for name,op,left,right in previous:
        if name in deleted:continue
        left,right=rename(left),rename(right)
        if name=='packed':name='raw_packed'
        ops.append((name,op,left,right))
        if name=='raw_packed':ops.append(('packed','+','raw_packed','Jwide'))
        if name=='D0':
            ops.extend([('twice_Jwide','+','Jwide','Jwide'),('wide_geometry','+','twice_Jwide',1)])
    pairs=[];source=[];origins=[];sub=native_substitution()
    for i,(pair,polynomial) in enumerate(zip(oldpairs,oldsource)):
        if i in (25,26,27,28):continue
        pair=tuple(rename(a) for a in pair)
        if i in (3,21):pair=(pair[0],'H')
        p=sp.expand(polynomial.subs(sub,simultaneous=True))
        if i==9:p=SYM['r']-sum(SYM[n]*SYM['q']**j for j,n in enumerate(FIELDS))-SYM['Jwide']
        pairs.append(pair);source.append(p);origins.append(i)
    pairs.append(('wide_geometry','D0'))
    source.append(2*SYM['Jwide']+1-SYM['q']**12);origins.append(None)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==110 and counts=={'+':55,'*':55}
    assert len(source)==len(pairs)==27 and len(OUTER_NAMES+CORE_NAMES)==39
    u=SYM['j']*SYM['c']+2*SYM['r']+1;records=[]
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        extra=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(env[left]-env[right]-p-extra)==0,(i,left,right)
        records.append(dict(index=i,old_index=origins[i],equality=[left,right],
                            source=sp.sstr(p),correction=sp.sstr(extra)))
    sub=native_substitution();previous=old.build()[2]
    blocksum=sum(SYM['q']**i for i in range(12))
    oldpacked=sp.expand(previous[9].subs(sub,simultaneous=True))
    assert sp.expand(2*(source[9]-oldpacked)+source[-1]+source[0]*blocksum)==0
    for i in (25,26,27,28):assert sp.expand(previous[i].subs(sub,simultaneous=True))==0
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(operations=110,primitive_histogram=counts,unknown_count=39,equations=27,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_offset_identity='2*(new_pack_residual-old_native_pack_residual)=-wide_geometry_residual-blocksum*old_q_geometry_residual',
                scope='Exact complete source/primitive schedule and integer offset identity; strict raw positivity and universality are separate proved obligations.')


def verify_offset_lemma():
    cases=0
    for q in (3,5,7,9,11,27,81):
        J=(q-1)//2;wide=(q**12-1)//2
        assert wide==J*sum(q**i for i in range(12))
        assert wide//q**11==J
        for a in (1,J,J+1,q-1,q,q+1):
            raw=[1]*11+[a]
            p=sum(v*q**i for i,v in enumerate(raw))
            r=p+wide
            assert r==sum((J+v)*q**i for i,v in enumerate(raw))
            if r<q**12:assert a<=J
            cases+=1
    words=0
    for ell in range(1,10):
        rep=(3**ell-1)//2
        for bits in range(1<<ell):
            raw=sum(((bits>>i)&1)*3**i for i in range(ell))
            assert native(raw+rep,ell)
            words+=1
    return dict(integer_offset_and_topfield_cases=cases,boolean_native_offset_words=words,
                scope='Offset identities include non-power q; native subtraction is checked independently on all Boolean words through nine ternary positions.')


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0;value_two_sources=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        aa,bb=ALIGNED.single.split_ternary(n,b)
        if n==2:
            assert aa==bb==1;value_two_sources+=1
        weight=R**b;A0+=aa*weight;A1+=bb*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight;last=(n,c['signs'][state],c['zeros'][state])
        values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and last==(1,-1,0) and value_two_sources>0
    D=H-Z;T=J-((R-3)//6)*D
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    TC=C+J-c['S']*H;TV=V+ZALL*H;wide=(q**12-1)//2
    z=dict(x=x,q=q,Jrep=J,W=W,H=H,v=q//W,R=R,T=T,A0=A0,A1=A1,
           B0=A0+T,B1=A1+T,Kp=Kp,Km=Km,Z=Z,Dzero=D,alphaI=R-2*x,
           PC=C,PV=V,PTC=TC,PTV=TV,Jwide=wide)
    raw=sum(z[n]*q**i for i,n in enumerate(FIELDS));r=raw+wide
    z['r']=r;z['beta']=q**12-r
    assert min(z.values())>0 and all(0<z[n]<q for n in FIELDS)
    assert r==sum((J+z[n])*q**i for i,n in enumerate(FIELDS))
    assert TV<=J and R-1>2*ZALL and 0<A0+A1<J and 0<T<J
    assert 0<V+c['hs']*Kp+c['hz']*D<TV and C<q
    ops,pairs,source,origins=build()
    indices=[i for i,origin in enumerate(origins) if origin is None or origin<10 or origin>=20]
    sub={SYM[n]:v for n,v in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(J+z[n],ell) for n in FIELDS)
    assert native(r,12*ell) and r%3==2 and r%2==0 and q**11<r<q**12<r*r
    val=central_valuation(r);assert val==12*ell
    return dict(x=x,serial_blocks=blocks,counter_width=c['B'],outer_residuals=len(indices),
                positive_raw_fields=len(FIELDS),value_two_sources=value_two_sources,
                packed_bits=r.bit_length(),valuation=val,
                scope='Full canonical source and all12 strictly positive raw fields, one shared offset, even unit-two index and every kernel bound. The existing six-state example already has true zero events; the general compiler prefix lemma is checked separately.')


def verify():
    return dict(status='PASS_GLOBAL_NATIVE_OFFSET_110',arithmetic=verify_certificate(),
                offset_lemma=verify_offset_lemma(),canonical=[canonical(1),canonical(2)],
                positive_raw_compiler=positivity.verify(),
                proof='../1980/EXPLORATION_GLOBAL_NATIVE_OFFSET.md',
                scope='Complete110-operation universal family with independent full proof/source and prefix audits and fresh verification. The stronger established universal frontier remains90.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['offset_lemma']);print(result['canonical'])
