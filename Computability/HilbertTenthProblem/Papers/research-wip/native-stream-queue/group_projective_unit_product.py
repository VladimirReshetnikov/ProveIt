"""Three integer units merge two Pell comparisons and the checksum.

An optional controller-mask reuse saves another multiplication for m>=8.
All degree/cost claims distinguish the four- and six-field parents.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_shifted_boundary as parent

range_parent=parent.parent.parent
execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def range_rewrite(old, controller_mask):
    if not controller_mask:return dict(old)
    assert old['m']>=8
    Pm=next(row[3] for row in old['source'] if row[0]=='joint_scale')
    replacements={'range_mask8':('*','range_cell','controller__origin_mask'),
                  'range_body_scale':('*','joint_scale',Pm)}
    source=[(name,*replacements[name]) if name in replacements else (name,op,a,b)
            for name,op,a,b in old['source'] if name!='range_origins']
    new=dict(old)
    new.update(source=source,operations=len(source),multiplications=old['multiplications']-1)
    assert new['operations']==old['operations']-1
    return new


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False):
    before=range_rewrite(parent.build(codes,alpha,beta,variant),controller_mask)
    replacements={
        'selection__R15':('-','selection__L15','selection__Ac2'),
        'selection__P17':('+','selection__L17','selection__aux_y2'),
        'selection__bs_q':('-','selection__q','selection__bs_Q')}
    source=[(name,*replacements[name]) if name in replacements else (name,op,a,b)
            for name,op,a,b in before['source']]
    source += [('unit_pair','*','selection__R15','selection__P17'),
               ('unit_product','*','unit_pair','selection__bs_q')]
    old_pairs=[('selection__L15','selection__R15'),
               ('selection__L17','selection__P17'),
               ('selection__bs_q','selection__q')]
    removed=[before['comparisons'].index(pair) for pair in old_pairs]
    pairs=[]
    for i,pair in enumerate(before['comparisons']):
        if i==min(removed):pairs.append(('unit_product',1))
        if i not in removed:pairs.append(pair)
    source=range_parent.sort_source(source,{'x',*before['auxiliaries']})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    packet=dict(before)
    packet.update(source=source,comparisons=pairs,operations=len(source),
                  multiplications=counts['M'],additions_subtractions=counts['A'],
                  equations=len(pairs),controller_mask=controller_mask,
                  scale_exponent=2*before['m']+10 if controller_mask else before['m']+18,
                  merged_comparison_indices=removed,merged_parent_comparisons=old_pairs)
    assert len(pairs)==before['equations']-2
    assert len(source)==before['operations']+2
    assert counts=={'M':before['multiplications']+2,'A':before['additions_subtractions']}
    return packet


def region_data(packet,z):
    v=range_parent.data(packet,z)
    if packet['controller_mask']:
        v['Rb']=(2*v['D']-1)*v['Mc']
        v['T2']=v['T']*z['P']**packet['m']
        v['N']=v['T2']*z['P']**2
        v['H']=v['H0']+v['T']*v['Hb']+v['T2']*v['B']
        v['M']=v['M0']+v['T']*v['Rb']+v['T2']*(v['B']-1)
        v['Z']=v['Z0']+v['T']*v['Hb']
    return v


def independent_parent_residuals(packet,z,env):
    restored=parent.parent.extend(packet,z,env)
    v=region_data(packet,restored);B,D,P=v['B'],v['D'],z['P'];shift=D-1
    initial=(D,shift+v['u'])*2;end=(shift,D)*2
    rr=[]
    for i in range(4):
        delta=z[f'Zhat{2*i}']-z[f'Zhat{2*i+1}']-shift*(v['S'][2*i]-v['S'][2*i+1])
        rr.append(B*(z[f'H{i}']+delta)-z[f'H{i}']-end[i]*P+initial[i])
    rr.append(sum(z[f'H{i}'] for i in range(4))+z['history_bound']-P)
    native=range_parent.shared.parent.selection.parent.native
    scalar={name:restored['selection__'+name] for name in range_parent.shared.parent.selection.parent.AUX}
    scalar.update(q=16*v['N'],F3=16*v['Z']+8)
    nr=list(native.independent_sources(scalar))
    U=scalar['j']*scalar['c']-(2*scalar['r']+1)
    nr[12]+=nr[11]*(U*U-scalar['y_aux']**2)
    rr+=nr
    rr += [scalar['F1']+scalar['F3']-16*v['H']-12,
           scalar['F2']+scalar['F3']-16*v['M']-10,
           sum(z[f'Zhat{i}'] for i in range(8))+z['selection__bound_global']-P-1,
           (B-1)*z['J']+1-P,packet['m']+z['controller__radix_beta']-B,
           sum(v['E'])-z['J'],
           sum((a-B*b)*v['E'][i] for i,(a,b,_) in enumerate(packet['edges']))]
    assert len(rr)==26
    return [rr[i] for i in packet['inherited_residual_indices']]


def expected_residuals(packet,before):
    main,aux,checksum=(before[i] for i in packet['merged_comparison_indices'])
    merged=(main+1)*(aux+1)*(1-checksum)-1
    answer=[]
    for i,value in enumerate(before):
        if i==min(packet['merged_comparison_indices']):answer.append(merged)
        if i not in packet['merged_comparison_indices']:answer.append(value)
    return answer


def source_checks():
    rng=random.Random(403268);records=[];cases=0
    tables=((),((1,2),),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        old=parent.build(codes,variant=variant)
        if reuse and old['m']<8:continue
        packet=build(codes,variant=variant,controller_mask=reuse)
        baseline=range_rewrite(old,reuse)
        sos,out=polynomial_source(packet)
        m,h,p=packet['m'],packet['h'],packet['projection_additions'];flow=packet['flow']['operations']
        assert packet['operations']==3*m+3*h+p+186+flow-3*min(h,3)-reuse
        assert packet['equations']==(20 if variant=='four' else 18)
        assert packet['positive_witnesses']==m+(36 if variant=='four' else 34)
        assert len(sos)==packet['operations']+3*packet['equations']-1
        assert len(sos)==len(polynomial_source(old)[0])-4-reuse
        for case in range(128):
            z={name:rng.randrange(1,11) if case<96 else rng.randrange(-5,6)
               for name in packet['parameters']+packet['auxiliaries']}
            env=execute(sos,z);oldenv=execute(baseline['source'],z)
            before=independent_parent_residuals(packet,z,env)
            assert residuals(baseline,oldenv)==before
            expected=expected_residuals(packet,before)
            assert residuals(packet,env)==expected and env[out]==sum(v*v for v in expected)
            for name,_,_,_ in packet['source']:
                if name not in ('selection__R15','selection__P17','selection__bs_q','unit_pair','unit_product'):
                    assert env[name]==oldenv[name]
            v=region_data(packet,z)
            for key in ('H','M','Z'):assert env['range_'+key]==v[key]
            assert env['selection__q']==16*v['N']
            if case<96:assert env['selection__F3']>=8
            cases+=1
        t=sp.Symbol('t');names=packet['parameters']+packet['auxiliaries']
        weights={name:1+i%3 for i,name in enumerate(names)}
        z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
        env=execute(sos,z);L=packet['scale_exponent'];w=weights
        qtop=16*w['P']**L;stop=2*w['selection__odd_half'];ktop=w['selection__eta']+w['selection__zeta']
        if variant=='four':
            degree=12*L+16
            top=w['selection__w']**2*stop**4*ktop**2*qtop**6
        else:
            astar=w['selection__w']*stop*qtop**2;ctop=ktop*stop*qtop
            rtop=16**4*w['H2']*w['P']**(3*L+m+15)
            top=(8*w['selection__ga']*astar**2*ctop)*(w['selection__i']**2*ctop**4*(2*rtop)**2)*qtop
            degree=32*L+4*m+98
        assert env[out].degree()==degree,(m,variant,reuse,env[out].degree(),degree)
        assert env[out].LC()==top**2,(m,variant,reuse,'leading form')
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
        packet['sum_of_squares']=dict(operations=len(sos),multiplications=counts['M'],additions_subtractions=counts['A'],exact_degree=degree,weighted_highest_coefficient=str(top**2),output=out)
        records.append(packet)
    return dict(packets=records,independent_complete_residual_and_SOS_cases=cases,signed_cases=cases//4)


def unit_checks():
    cases=0
    for a in range(4):
      for d in range(4):
       for c in range(4):
        assert (d*d-((a+2)**2-1)*c*c)%4!=3
        cases+=1
    for T in range(4):
      for U in range(4):
       for y in range(4):
        assert (T*T*(U*U-y*y)+y*y)%4!=3
        cases+=1
    return dict(complete_residue_classes=cases,lemma='An integer product1 has only unit factors; both norm factors exclude-1 modulo4.')


def mask_checks():
    rng=random.Random(810134);cases=0
    for m in (8,16,32):
      for _ in range(128):
        D=1<<rng.randrange(2,6);B=8*D;t=rng.randrange(1,5);P=B**t;J=(P-1)//(B-1)
        E=[0]*m;S=[[0]*t for _ in range(8)]
        for j in range(t):
            e=rng.randrange(m);E[e]+=B**j
            label=rng.randrange(9)
            if label:S[label-1][j]=1
        rows=[[rng.randrange(2*D) for _ in range(4)] for _ in range(t)]
        for i in range(4):rows[0][i]=max(rows[0][i],1)
        hist=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
        selected=[sum(S[i][j]*rows[j][(i//2)^1]*B**j for j in range(t)) for i in range(8)]
        Hb=sum(hist[(i//2)^1]*P**i for i in range(8));Mb=(B-1)*sum(sum(S[i][j]*B**j for j in range(t))*P**i for i in range(8));Zb=sum(selected[i]*P**i for i in range(8))
        Hc=sum(E[i]*P**i for i in range(m));Mc=J*sum(P**i for i in range(m));T=P**(m+8)
        H0=Hb+P**8*Hc;M0=Mb+P**8*Mc;Z0=Zb+P**8*Hc
        R=(2*D-1)*Mc;T2=T*P**m;N=T2*P**2
        H=H0+T*Hb+T2*B;M=M0+T*R+T2*(B-1);Z=Z0+T*Hb
        assert 0<=R<P**m and 0<=H<N and 0<=M<N
        assert Hb&R==Hb and H&M==Z
        assert sum(hist)<P and P-sum(selected)-7>0
        if m==8:assert R==(2*D-1)*J*sum(P**i for i in range(8))
        # A forbidden low-cell bit cannot survive the reused mask.
        malformed=2*D*P**rng.randrange(8)
        assert malformed&R!=malformed
        cases+=1
    return dict(joined_AND_and_positive_bound_cases=cases,including_m8_identity=True)


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_UNIT_PRODUCT',source=source_checks(),unit_mod4=unit_checks(),controller_mask=mask_checks(),
                default_polynomial_saving_from_shifted_parent=4,controller_mask_additional_saving=1,
                scope='Complete positive compiler equivalence; mask reuse requires m>=8. No numerical universal alphabet is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
