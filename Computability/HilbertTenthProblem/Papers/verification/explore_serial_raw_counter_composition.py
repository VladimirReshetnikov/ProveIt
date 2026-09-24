#!/usr/bin/env python3
"""Exact123 serial fixed-program control for three raw numerical counters."""
from pathlib import Path
import json
import sympy as sp
import explore_labelled_raw_counter_composition as frame
import explore_parity_aligned_raw_counters as aligned
from explore_native_ternary_ripple import native,central_valuation


def program_constants():
    m=6;l=2;prime=11;N=m+2
    marks=[2*prime*i+(i*i)%prime for i in range(N)]
    shift=max(marks)+1;coords=[l*(shift+mark) for mark in marks]
    a=coords[:m];bs,bz=coords[m:];d=bz
    assert len({coords[i]+coords[j] for i in range(N) for j in range(i,N)})==N*(N+1)//2
    assert 2*min(coords)>max(coords)
    phases=[0,1,2,0,1,2];signs=[1,1,1,-1,-1,-1];zeros=[0,1,1,0,0,0]
    edges=[(0,1),(1,2),(2,3),(3,4),(3,1),(4,5),(5,3),(5,0)]
    assert all(phases[j]==(phases[i]+1)%3 for i,j in edges)
    positions=[d+a[j]-a[i] for i,j in edges]+[d-a[i] for i in range(m)]
    positions += [d+bs-a[i] for i in range(m) if signs[i]==1]
    positions += [d+bz-a[i] for i in range(m) if zeros[i]]
    assert min(positions)>=0 and len(set(positions))==len(positions)
    K=sum(3**e for e in positions);S=sum(3**e for e in a);g=3**d
    hs=3**(d+bs);hz=3**(d+bz);Zc=sum(3**(d+h) for h in range(1,l))
    B=2;Rmin=9
    while Rmin<=max(K*S,g*S,2*S+1,Zc+hs+hz):B+=2;Rmin*=9
    return dict(m=m,l=l,prime=prime,coords=coords,a=a,bs=bs,bz=bz,d=d,phases=phases,
                signs=signs,zeros=zeros,edges=edges,positions=positions,K=K,S=S,g=g,hs=hs,hz=hz,
                Zc=Zc,B=B,Rmin=Rmin,I=3**a[0],F=3**a[0],initial=0,final=0)


PROGRAM=program_constants()
BASE_SYM,BASE_OUTER=aligned.symbols(3)
OUTER_NAMES=BASE_OUTER+frame.NEW_NAMES
CORE_NAMES=aligned.single.CORE_NAMES
SYM={n:sp.Symbol(n) for n in ['x']+OUTER_NAMES+CORE_NAMES}
FIELDS=frame.FIELDS


def build():
    c=PROGRAM;instructions=[]
    dropped={'W_minus_one','time_head_product','history_product','control_product','time_partial',
             'K_R_high','K_R_mid','K_R_low','K_R','flag_forbidden','junk_forbidden'}
    for name,op,left,right in frame.build()[0]:
        if name in dropped:continue
        if name=='time_lhs':
            instructions.extend([('next_A','+','raw_A','delta'),('time_lhs','*','W','next_A'),('time_rhs','-','raw_A','input')]);continue
        if left=='Htime':left='H'
        if right=='Htime':right='H'
        if name=='program_support':left=c['S']
        if name=='marker_forbidden':left=c['Zc']+c['hs']+c['hz']
        if name=='program_V_rhs':left,right='PV','marker_forbidden'
        if name=='program_R_bound':left=c['Rmin']
        if name=='WK':left,right='R',c['K']
        if name=='route_coeff':right=c['g']
        if name=='route_lhs':right=c['g']*c['I']
        if name=='sign_output':left=c['hs']
        if name=='zero_output':left=c['hz']
        if name=='route_junkW':left='R'
        if name=='route_final':left=c['g']*c['F']
        instructions.append((name,op,left,right))
    pairs=aligned.equalities(3);pairs[4]=('top_mask','top_rhs')
    pairs += frame.build()[1][23:]
    z=SYM;q,J,R,W,H=[z[n] for n in ['q','Jrep','R','W','H']]
    source=[p.subs({BASE_SYM[n]:z[n] for n in BASE_SYM},simultaneous=True) for p in aligned.source_residuals(3)]
    source[4]=6*z['T']-2*(2*J+H)-(R-3)*(z['FZ']-J)
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));source[10]=z['r']-P
    sub={aligned.single.kernel.SYM[n]:z[n] for n in CORE_NAMES};sub[aligned.single.kernel.SYM['D0']]=q**12
    source[11:21]=[p.subs(sub,simultaneous=True) for p in aligned.single.kernel.source_residuals(1)]
    source += [2*z['T']+z['alphaT']-q,z['FZ']+z['FZbar']-2*J-H,
        z['PC']+J-c['S']*H-z['PTC'],z['PTV']-z['PV']-(c['Zc']+c['hs']+c['hz'])*H,
        z['PTC']+z['PTV']+z['alphaP']-q,
        z['PNC']-J-z['PC'],z['PNV']-J-z['PV'],z['PNTC']-J-z['PTC'],z['PNTV']-J-z['PTV'],
        R-c['Rmin']*z['zR'],(R*c['K']-c['g'])*z['PC']+c['g']*c['I']-c['g']*c['F']*q
        -R*(z['PV']+c['hs']*(z['FKplus']-J)+c['hz']*(z['FZ']-J))]
    return instructions,pairs,source


def verify_certificate():
    instructions,pairs,source=build();env=dict(SYM)
    hist=aligned.baseline.run_schedule(instructions,env);records=[]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[18]*(u*u-SYM['y_aux']**2) if i==19 else 0
        assert sp.expand(actual-p-extra)==0,i
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=aligned.verify_primitives(instructions,env)
    assert len(primitive)==123 and counts=={'+':67,'*':56},(len(primitive),counts)
    assert len(source)==len(pairs)==33 and len(OUTER_NAMES+CORE_NAMES)==45
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=123,primitive_histogram=counts,histogram=hist,parameters=['x'],
                positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=45,equations=33,
                primitive_instructions=primitive,equalities=pairs,residuals=records,fixed_program=PROGRAM)


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0];blocks=len(path)-1
    R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0;zero_events=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane
        assert (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0;zero_events+=1
        a,d=aligned.single.split_ternary(n,b);weight=R**b
        A0+=a*weight;A1+=d*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight
        values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and blocks%6==0
    T=R//3*H+(R-3)//6*Z
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*Z
    TC=C+J-c['S']*H;TV=V+(c['Zc']+c['hs']+c['hz'])*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
        F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
        FZ=J+Z,FZbar=J+H-Z,alpha=J+1-A0-A1,alphaI=R-2*x,alphaT=q-2*T,
        PC=C,PV=V,PTC=TC,PTV=TV,alphaP=q-TC-TV,PNC=J+C,PNV=J+V,PNTC=J+TC,PNTV=J+TV,zR=1)
    assert min(z.values())>0
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));z['r']=P
    source=build()[2];indices=list(range(11))+list(range(21,len(source)))
    substitutions={SYM[n]:value for n,value in z.items()}
    assert all(source[i].subs(substitutions,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(z[n],ell) and z[n]<q for n in FIELDS)
    assert native(P,12*ell) and P%3==2 and P%2==0 and P<q**12
    assert central_valuation(P)==12*ell and q**12<P*P
    return dict(x=x,path=path,block_steps=blocks,bank_rounds=blocks//3,counter_width=c['B'],
                zero_event_count=zero_events,outer_residuals=len(indices),packed_bits=P.bit_length(),valuation=12*ell,
                full_positive_extension='All native, parity and general-scale hypotheses of the complete fixed-sign43 converse hold.')


def verify():
    return dict(status='PASS_SERIAL_RAW_COUNTER_COMPOSITION_123',arithmetic=verify_certificate(),
                canonical=[canonical(1),canonical(2)],proof='../1980/EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md',
                scope='Exact serial finite-state labelled control of three raw numerical counters, including paid zero tests. No universal compiler or improved universal bound is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram']);print(result['canonical'])
