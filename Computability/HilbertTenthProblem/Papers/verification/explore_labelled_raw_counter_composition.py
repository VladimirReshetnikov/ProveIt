#!/usr/bin/env python3
"""Fully shared frame-controller baseline: three raw counters and zero tests."""
from pathlib import Path
import json
import sympy as sp
import explore_simultaneous_raw_ternary_counters as counter
from explore_native_ternary_ripple import native,central_valuation


def program_constants():
    m=3;l=2;a=[l*3**i for i in range(m)];bs=l*3**m;bz=l*3**(m+1);d=bz
    edges=[(0,1),(1,0),(1,2),(2,1)]
    signs=[(1,1,1),(-1,-1,-1),(-1,1,1)]
    zeros=[(0,1,1),(0,0,0),(0,1,1)]
    base=[d+a[j]-a[i] for i,j in edges]+[d-a[i] for i in range(m)]
    positions=[]
    for lane in range(3):
        terms=base[:] if lane==0 else []
        terms += [d+bs-a[i] for i in range(m) if signs[i][lane]==1]
        terms += [d+bz-a[i] for i in range(m) if zeros[i][lane]]
        assert len(terms)==len(set(terms));positions.append(terms)
    K=[sum(3**e for e in terms) for terms in positions]
    S=sum(3**e for e in a);g=3**d;hs=3**(d+bs);hz=3**(d+bz)
    Zc=sum(3**(d+h) for h in range(1,l));B=2;Rmin=9
    while Rmin<=max(*(Ki*S for Ki in K),g*S,2*S+1,Zc+hs+hz):B+=2;Rmin*=9
    return dict(m=m,l=l,a=a,d=d,edges=edges,signs=signs,zeros=zeros,K=K,S=S,g=g,hs=hs,hz=hz,
                Zc=Zc,B=B,Rmin=Rmin,initial=0,final=0,I=3**a[0],F=3**a[0])


PROGRAM=program_constants()
NEW_NAMES=['FZ','FZbar','alphaT','PC','PV','PTC','PTV','alphaP','PNC','PNV','PNTC','PNTV','zR']
OUTER_NAMES=counter.OUTER_NAMES+NEW_NAMES
SYM={n:sp.Symbol(n) for n in counter.PARAMETERS+OUTER_NAMES+counter.CORE_NAMES}
FIELDS=counter.FIELDS+['FZ','FZbar','PNC','PNV','PNTC','PNTV']


def build():
    c=PROGRAM;S,g,hs,hz,Zc,Rmin=[c[n] for n in ['S','g','hs','hz','Zc','Rmin']];K0,K1,K2=c['K']
    prefix=[]
    for row in counter.schedule(3):
        name=row[0]
        if name.startswith('pack') or name=='packed':continue
        if name=='q2':break
        if name=='top_mask':
            prefix.extend([('twice_T','+','T','T'),('top_mask','*',3,'twice_T'),
                ('twice_head','+','head_rhs','head_rhs'),('R_minus_three','-','R_minus_one',2),
                ('raw_Z','-','FZ','Jrep'),('zero_spread','*','R_minus_three','raw_Z'),
                ('top_rhs','+','twice_head','zero_spread'),('top_bound','+','twice_T','alphaT'),
                ('zero_flag_sum','+','FZ','FZbar')])
        else:prefix.append(row)
    prefix.extend([
        ('program_support','*',S,'Htime'),('program_C_lhs','+','PC','Jrep'),
        ('program_C_rhs','+','program_support','PTC'),
        ('marker_forbidden','*',Zc,'Htime'),('flag_forbidden','*',hs+hz,'H'),
        ('junk_forbidden','+','PV','marker_forbidden'),('program_V_rhs','+','junk_forbidden','flag_forbidden'),
        ('program_bound_sum','+','PTC','PTV'),('program_bound','+','program_bound_sum','alphaP'),
        ('program_native_C','+','Jrep','PC'),('program_native_V','+','Jrep','PV'),
        ('program_native_TC','+','Jrep','PTC'),('program_native_TV','+','Jrep','PTV'),
        ('program_R_bound','*',Rmin,'zR'),
        ('K_R_high','*','R',K2),('K_R_mid','+',K1,'K_R_high'),
        ('K_R_low','*','R','K_R_mid'),('K_R','+',K0,'K_R_low'),
        ('WK','*','W','K_R'),('route_coeff','-','WK',g),
        ('route_product','*','route_coeff','PC'),('route_lhs','+','route_product',g*c['I']),
        ('raw_Kplus','-','FKplus','Jrep'),('sign_output','*',hs,'raw_Kplus'),
        ('zero_output','*',hz,'raw_Z'),('route_junk1','+','PV','sign_output'),
        ('route_junk2','+','route_junk1','zero_output'),('route_junkW','*','W','route_junk2'),
        ('route_final','*',g*c['F'],'q'),('route_rhs','+','route_final','route_junkW'),
    ])
    prior=FIELDS[-1]
    for i,field in enumerate(reversed(FIELDS[:-1])):
        p=f'pack_product{i}';v='packed' if i==len(FIELDS)-2 else f'pack_sum{i}'
        prefix.extend([(p,'*','q',prior),(v,'+',field,p)]);prior=v
    powers=[('q2','*','q','q'),('q4','*','q2','q2'),('q6','*','q4','q2'),('D0','*','q6','q6')]
    instructions=prefix+powers+counter.old.kernel.schedule(1)
    tests=counter.equalities();tests[4]=('top_mask','top_rhs')
    tests += [('top_bound','q'),('zero_flag_sum','head_rhs'),
        ('program_C_lhs','program_C_rhs'),('PTV','program_V_rhs'),('program_bound','q'),
        ('PNC','program_native_C'),('PNV','program_native_V'),('PNTC','program_native_TC'),('PNTV','program_native_TV'),
        ('R','program_R_bound'),('route_lhs','route_rhs')]
    source=[p.subs({counter.SYM[n]:SYM[n] for n in counter.SYM},simultaneous=True) for p in counter.source_residuals(3)]
    z=SYM;q,J,R,W,H,Ht=[z[n] for n in ['q','Jrep','R','W','H','Htime']]
    source[4]=6*z['T']-2*(2*J+H)-(R-3)*(z['FZ']-J)
    packed=sum(z[n]*q**i for i,n in enumerate(FIELDS));source[10]=z['r']-packed
    sub={counter.old.kernel.SYM[n]:z[n] for n in counter.CORE_NAMES};sub[counter.old.kernel.SYM['D0']]=q**12
    source[11:21]=[p.subs(sub,simultaneous=True) for p in counter.old.kernel.source_residuals(1)]
    Kpoly=K0+R*(K1+R*K2)
    source += [2*z['T']+z['alphaT']-q,z['FZ']+z['FZbar']-2*J-H,
        z['PC']+J-S*Ht-z['PTC'],z['PTV']-z['PV']-Zc*Ht-(hs+hz)*H,
        z['PTC']+z['PTV']+z['alphaP']-q,
        z['PNC']-J-z['PC'],z['PNV']-J-z['PV'],z['PNTC']-J-z['PTC'],z['PNTV']-J-z['PTV'],
        R-Rmin*z['zR'],(W*Kpoly-g)*z['PC']+g*c['I']-g*c['F']*q-W*(z['PV']+hs*(z['FKplus']-J)+hz*(z['FZ']-J))]
    return instructions,tests,source


def verify_certificate():
    instructions,tests,source=build();env=dict(SYM);env['zero']=sp.Integer(0)
    hist=counter.baseline.run_schedule(instructions,env);records=[]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for i,((left,right),p) in enumerate(zip(tests,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[18]*(u*u-SYM['y_aux']**2) if i==19 else 0
        assert sp.expand(actual-p-extra)==0,i
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=counter.verify_primitives(instructions,env)
    assert len(primitive)==132 and counts=={'+':71,'*':61},(len(primitive),counts)
    assert len(source)==len(tests)==34 and len(OUTER_NAMES+counter.CORE_NAMES)==46
    return dict(status='PASS',operations=132,primitive_histogram=counts,histogram=hist,
                positive_unknowns=OUTER_NAMES+counter.CORE_NAMES,unknown_count=46,parameters=['x'],
                equations=34,primitive_instructions=primitive,equalities=tests,residuals=records,
                fixed_program=PROGRAM,scope='Exact arithmetic for the fully specified frame-controller baseline; semantic proof and finite tests accompany this certificate.')


def canonical(x):
    c=PROGRAM;path=[0,1]+[2,1]*x+[0];height=len(path)-1
    R=c['Rmin'];W=R**3;q=W**height;J=(q-1)//2;H=(q-1)//(R-1);Ht=(q-1)//(W-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
    for t,state in enumerate(path[:-1]):
        for lane in range(3):
            bit=c['zeros'][state][lane]
            assert not bit or values[lane]==0
            n=values[lane];assert 0<=n<R//3
            a,b=counter.old.split_ternary(n,t+lane);weight=R**(3*t+lane)
            A0+=a*weight;A1+=b*weight
            if c['signs'][state][lane]==1:Kp+=weight
            else:Km+=weight
            Z+=bit*weight
        values=[n+sgn for n,sgn in zip(values,c['signs'][state])];assert min(values)>=0
    assert values==[0,0,0]
    T=R//3*H+(R-3)//6*Z
    PC=sum(3**c['a'][state]*W**t for t,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*W**t for t,state in enumerate(path[1:]))
    KR=c['K'][0]+R*(c['K'][1]+R*c['K'][2])
    PV=KR*PC-c['g']*Next-c['hs']*Kp-c['hz']*Z
    PTC=PC+J-c['S']*Ht;PTV=PV+c['Zc']*Ht+(c['hs']+c['hz'])*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,Htime=Ht,v=q//W,T=T,
        F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
        FZ=J+Z,FZbar=J+H-Z,alpha=J+1-A0-A1,alphaI=R-2*x,alphaT=q-2*T,
        PC=PC,PV=PV,PTC=PTC,PTV=PTV,alphaP=q-PTC-PTV,
        PNC=J+PC,PNV=J+PV,PNTC=J+PTC,PNTV=J+PTV,zR=1)
    assert min(z.values())>0
    packed=sum(z[n]*q**i for i,n in enumerate(FIELDS));z['r']=packed
    instructions,tests,source=build()
    # Outer verification evaluates no enormous Pell coordinates.
    outer_indices=list(range(11))+list(range(21,len(source)))
    substitutions={SYM[name]:value for name,value in z.items()}
    assert all(source[i].subs(substitutions,simultaneous=True)==0 for i in outer_indices)
    ell=c['B']*3*height
    assert all(native(z[name],ell) and z[name]<q for name in FIELDS)
    assert native(packed,12*ell) and packed%3==2 and packed%2==0
    assert packed<q**12 and central_valuation(packed)==12*ell
    assert q**12>=81 and packed>=27 and packed<2*q**12 and q**12<packed*packed
    return dict(x=x,path=path,time_height=height,counter_width=c['B'],outer_residuals=len(outer_indices),
                packed_bits=packed.bit_length(),valuation=12*ell,zero_event_count=sum(sum(c['zeros'][s]) for s in path[:-1]),
                full_positive_extension='All outer witnesses, native masks, even index and general-scale bounds meet the complete fixed-sign43 Pell positive converse.')


def verify():
    return dict(status='PASS_LABELLED_RAW_COUNTER_COMPOSITION_132',arithmetic=verify_certificate(),
                canonical=[canonical(x) for x in (1,2)],
                proof='../1980/EXPLORATION_LABELLED_RAW_COUNTER_COMPOSITION.md',
                scope='Complete fixed labelled-graph controller for three raw counters, including source zero tests and all shared arithmetic. No optimized universal-machine bound is asserted.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram']);print(result['canonical'])
