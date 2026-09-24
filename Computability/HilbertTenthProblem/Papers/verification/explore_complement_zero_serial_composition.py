#!/usr/bin/env python3
"""Exact117: emit the complementary zero label and factor its top mask."""
from pathlib import Path
import json
import sympy as sp
import explore_cyclic_entry_serial_composition as old
from explore_native_ternary_ripple import native, central_valuation


SYM=old.SYM
OUTER_NAMES=old.OUTER_NAMES
CORE_NAMES=old.CORE_NAMES
FIELDS=old.old.FIELDS
PROGRAM=dict(old.PROGRAM)
positions=[PROGRAM['d']+PROGRAM['a'][j]-PROGRAM['a'][i] for i,j in PROGRAM['edges']]
positions += [PROGRAM['d']-a for a in PROGRAM['a']]
positions += [PROGRAM['d']+PROGRAM['bs']-PROGRAM['a'][i] for i in range(PROGRAM['m']) if PROGRAM['signs'][i]==1]
positions += [PROGRAM['d']+PROGRAM['bz']-PROGRAM['a'][i] for i in range(PROGRAM['m']) if PROGRAM['zeros'][i]==0]
assert len(positions)==len(set(positions)) and min(positions)>=0
PROGRAM['positions']=positions
PROGRAM['K']=sum(3**e for e in positions)
PROGRAM['emitted_nozero']=[1-z for z in PROGRAM['zeros']]
ZALL=PROGRAM['Zc']+PROGRAM['hs']+PROGRAM['hz']
M=PROGRAM['K']*PROGRAM['S']+ZALL
while PROGRAM['Rmin']<=max(PROGRAM['K']*PROGRAM['S'],PROGRAM['g']*PROGRAM['S'],
                            2*PROGRAM['S']+1,ZALL,12*(M+1)):
    PROGRAM['Rmin']*=9;PROGRAM['B']+=2
assert PROGRAM['Rmin']%old.PROGRAM['Rmin']==0


def build():
    prior_ops,prior_pairs,prior_source=old.build();ops=[]
    for name,op,left,right in prior_ops:
        if name in ('twice_head','top_rhs'):continue
        if name=='top_mask':
            ops.append(('top_complement','-','Jrep','T'));right='top_complement'
        if name=='raw_Z':name,left='raw_D','FZbar'
        if name=='zero_spread':right='raw_D'
        if name=='zero_output':name,right='nozero_output','raw_D'
        if name=='route_junk2':right='nozero_output'
        if name=='WK':right=PROGRAM['K']
        if name=='program_R_bound':left=PROGRAM['Rmin']
        ops.append((name,op,left,right))
    pairs=list(prior_pairs);pairs[4]=('top_mask','zero_spread')
    source=list(prior_source);z=SYM;c=PROGRAM
    source[4]=6*(z['Jrep']-z['T'])-(z['R']-3)*(z['FZbar']-z['Jrep'])
    source[29]=z['R']-c['Rmin']*z['zR']
    source[30]=(z['R']*c['K']-c['g'])*z['PC']-2*c['g']*c['I']*z['Jrep'] \
        -z['R']*(z['PV']+c['hs']*(z['FKplus']-z['Jrep'])+c['hz']*(z['FZbar']-z['Jrep']))
    return ops,pairs,source


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM)
    hist=old.old.old.old.aligned.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitive)==117 and counts=={'+':61,'*':56}
    assert len(source)==len(pairs)==31 and len(OUTER_NAMES+CORE_NAMES)==43
    prior=old.build()[2];z=SYM
    assert sp.expand(source[4]+prior[4]+prior[2]+(z['R']-3)*prior[21])==0
    u=z['j']*z['c']+2*z['r']+1;records=[]
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right])
        extra=source[17]*(u*u-z['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,i
        if i not in (4,29,30):assert p==prior[i]
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    used={v for row in ops for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used
    assert not (used&{'twice_head','top_rhs','raw_Z','zero_output'})
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=117,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=43,
                equations=31,primitive_instructions=primitive,equalities=pairs,residuals=records,
                fixed_program=PROGRAM,
                exact_delta=dict(deleted_registers=['twice_head','top_rhs'],new_register='top_complement=Jrep-T',
                    raw_label='raw_D=FZbar-Jrep, shared between zero_spread and nozero_output',
                    top_residual='new=-old-head_geometry-(R-3)*zero_flag_pair',
                    unchanged_source_count=28,
                    semantic_label='original zero request z_i remains; the fixed ROM emits1-z_i'))


def verify_zero_identities():
    cases=label_cases=0
    for R in (9,27,81,243):
        for blocks in range(1,9):
            q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
            for flags in range(1<<blocks):
                Z=sum(((flags>>b)&1)*R**b for b in range(blocks));D=H-Z
                T=(R//3)*H+((R-3)//6)*Z
                assert 6*(J-T)==(R-3)*D
                assert 0<T<=J and native(J+Z,blocks*round_log(R)) and native(J+D,blocks*round_log(R))
                for b in range(blocks):
                    z=(Z//R**b)%R;d=(D//R**b)%R;t=(T//R**b)%R
                    assert z==1-d and t==((R-1)//2 if z else R//3)
                    label_cases+=1
                cases+=1
    c=PROGRAM
    for i in range(c['m']):
        row=c['K']*3**c['a'][i]
        assert row<c['Rmin']
        assert (row//c['hz'])%3==1-c['zeros'][i]
        assert (row//c['hs'])%3==int(c['signs'][i]==1)
        assert (row//c['g'])%3==1
        for j in range(c['m']):
            assert (row//(c['g']*3**c['a'][j]))%3==int((i,j) in c['edges'])
    return dict(complete_zero_head_sets=cases,individual_zero_block_checks=label_cases,
                fixed_source_rows=c['m'],
                scope='Both zero polarities, including all/no requests, obey the exact complement equation and the unchanged true-zero guard; fixed ROM rows check all state/sign/complement outputs.')


def round_log(R):
    m=0
    while R>1:assert R%3==0;R//=3;m+=1
    return m


def canonical(x):
    c=PROGRAM;path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0];blocks=len(path)-1
    R=c['Rmin'];W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0;zero_events=0;last_source=None
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0;zero_events+=1
        # The ordinary numerical digit split is the frozen raw-component routine.
        first,second=old.old.old.old.aligned.single.split_ternary(n,b)
        weight=R**b;A0+=first*weight;A1+=second*weight
        if c['signs'][state]==1:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight
        last_source=(n,c['signs'][state],c['zeros'][state])
        values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and blocks%6==0 and last_source==(1,-1,0)
    D=H-Z;T=(R//3)*H+((R-3)//6)*Z
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    TC=C+J-c['S']*H;TV=V+ZALL*H
    z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,v=q//W,T=T,
        F0=J+A0,F1=J+A1,G0=J+A0+T,G1=J+A1+T,FKplus=J+Kp,FKminus=J+Km,
        FZ=J+Z,FZbar=J+D,alphaI=R-2*x,PC=C,PV=V,PTC=TC,PTV=TV,
        beta=q-T-TC-TV,PNC=J+C,PNV=J+V,PNTC=J+TC,PNTV=J+TV,zR=1)
    assert min(z.values())>0 and 6*(J-T)==(R-3)*D
    assert TC+TV==J+C+V+(ZALL-c['S'])*H>J
    assert T<=q//3+(q//R-1)//2 and TC<=J and TV<M*H
    P=sum(z[n]*q**i for i,n in enumerate(FIELDS));z['r']=P
    source=build()[2];indices=list(range(10))+list(range(20,len(source)))
    sub={SYM[n]:value for n,value in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in indices)
    ell=c['B']*blocks
    assert all(native(z[n],ell) and z[n]<q for n in FIELDS)
    assert native(P,12*ell) and P%3==2 and P%2==0 and P<q**12
    assert central_valuation(P)==12*ell and q**12<P*P
    assert q**12>=81 and P>=27 and P<2*q**12
    return dict(x=x,path=path,block_steps=blocks,bank_rounds=blocks//3,counter_width=c['B'],
                true_zero_events=zero_events,emitted_nozero_events=blocks-zero_events,last_source=list(last_source),
                outer_residuals=len(indices),packed_bits=P.bit_length(),valuation=12*ell,
                positive_beta=True,top_complement=bool(J-T>0),
                full_positive_extension='Every native field, even unit-two packed index, general-scale bound and positive merged slack is checked. The complete fixed-sign43 converse supplies the unmaterialized Pell witnesses.')


def verify():
    return dict(status='PASS_COMPLEMENT_ZERO_SERIAL_COMPOSITION_117',arithmetic=verify_certificate(),
                zero_interface=verify_zero_identities(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_COMPLEMENT_ZERO_SERIAL_COMPOSITION.md',
                scope='Complete117-operation cyclic serial raw-counter universal family. The ROM emits the complementary auxiliary label; true source-zero tests and all twelve native fields are preserved. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['zero_interface']);print(result['canonical'])
