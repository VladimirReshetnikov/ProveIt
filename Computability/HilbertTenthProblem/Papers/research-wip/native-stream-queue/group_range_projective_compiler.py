"""Range-typed signed histories replace the entire duration-height kernel.

The exact generic relation is paired action on(-1,u), ending at e2.
The special universal subgroup theorem supplies its universal-query use.
"""
import argparse
from collections import Counter
import heapq
import json
from pathlib import Path
import random

import sympy as sp
import group_computed_selector_ports as previous
import group_shared_typing_matrix_compiler as shared
import group_four_register_history as physical


def sort_source(source, supplied):
    producer={name:i for i,(name,_,_,_) in enumerate(source)}
    assert len(producer)==len(source) and not set(supplied).intersection(producer)
    users=[[] for _ in source];pending=[];ready=[]
    for i,(_,_,a,b) in enumerate(source):
        deps={v for v in (a,b) if isinstance(v,str) and v not in supplied}
        assert deps<=producer.keys()
        pending.append(len(deps))
        for dep in deps:users[producer[dep]].append(i)
        if not deps:heapq.heappush(ready,i)
    result=[]
    while ready:
        i=heapq.heappop(ready);result.append(source[i])
        for j in users[i]:
            pending[j]-=1
            if pending[j]==0:heapq.heappush(ready,j)
    assert len(result)==len(source)
    return result


def build(codes, alpha=24, beta=12):
    old=previous.build(codes,alpha,beta)
    boundary_names={'history__input_product','history__r','D','history__c0','history__d0',
                    'history__rq','history__z','history__U','history__rz','history__V'}
    removed_boundary=[row for row in old['source'] if row[0] in boundary_names]
    removed_geometry=[row for row in old['source'] if row[0].startswith('geometry__')]
    assert len(removed_boundary)==10 and len(removed_geometry)==47
    assert Counter('M' if op=='*' else 'A' for _,op,_,_ in removed_geometry)=={'M':26,'A':21}
    boundary=[('history__input_product','*',alpha,'x'),
              ('history__u','+','history__input_product',beta+1),
              ('D','+','history__u','height_slack'),
              ('history__c0','-','D',1),
              ('history__d0','+','D','history__u'),
              ('history__V','+','D',1)]
    def resolve(name):
        while name in old['common_register_aliases']:
            name=old['common_register_aliases'][name]
        return name
    P2,P8,K8=map(resolve,('selection__P2','selection__P8','selection__J8'))
    added=[('range_cell','+','D','history__c0'),
           ('range_origins','*','range_cell','J'),
           ('range_mask8','*','range_origins',K8),
           ('range_body_scale','*','joint_scale',P8),
           ('range_history_shift','*','joint_scale','selection__Hbatch'),
           ('range_mask_shift','*','joint_scale','range_mask8'),
           ('range_Hbody','+','joint_H','range_history_shift'),
           ('range_Mbody','+','joint_M','range_mask_shift'),
           ('range_Z','+','joint_Z','range_history_shift'),
           ('range_Bshift','*','range_body_scale','B'),
           ('range_Bminus_shift','*','range_body_scale','controller__cell_minus1'),
           ('range_H','+','range_Hbody','range_Bshift'),
           ('range_M','+','range_Mbody','range_Bminus_shift'),
           ('range_total_scale','*','range_body_scale',P2)]
    assert Counter('M' if op=='*' else 'A' for _,op,_,_ in added)=={'M':8,'A':6}
    replacements={'selection__q':('*',16,'range_total_scale'),
                  'selection__scaled_A':('*',16,'range_H'),
                  'selection__scaled_B':('*',16,'range_M'),
                  'selection__scaled_Z':('*',16,'range_Z')}
    source=list(boundary)
    for name,op,a,b in old['source']:
        if name in boundary_names or name.startswith('geometry__'):continue
        if name in replacements:op,a,b=replacements[name]
        a='D' if a=='history__U' else a
        b='D' if b=='history__U' else b
        source.append((name,op,a,b))
    source+=added
    auxiliaries=[name for name in old['auxiliaries'] if not name.startswith('geometry__') and name!='q_geom']
    auxiliaries.insert(0,'height_slack')
    assert len(old['auxiliaries'])-len(auxiliaries)==19
    source=sort_source(source,{'x',*auxiliaries})
    pairs=list(old['comparisons'][:26])
    assert all(not(isinstance(v,str) and v.startswith('geometry__')) for pair in pairs for v in pair)
    assert not any('q_geom' in row for row in source)
    m,h,p=old['m'],old['h'],old['projection_additions'];f=old['flow']
    dm=old['common_register_saving']['multiplications'];da=old['common_register_saving']['additions_subtractions']
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':m+2*h+80+f['multiplications']-dm,'A':2*m+h+p+105+f['additions_subtractions']-da}
    assert len(source)==old['operations']-37==3*m+3*h+p+185+f['operations']-3*min(h,3)
    assert len(pairs)==26 and len(auxiliaries)==m+40
    return dict(codes=old['codes'],edges=old['edges'],alpha=alpha,beta=beta,m=m,h=h,
                projection_additions=p,flow=f,common_register_saving=old['common_register_saving'],
                parameters=['x'],auxiliaries=auxiliaries,source=source,comparisons=pairs,
                operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
                equations=26,positive_witnesses=len(auxiliaries),boundary_source=boundary,
                added_range_source=added,removed_geometry_source=removed_geometry,
                removed_boundary_source=removed_boundary)


def data(packet,z):
    m=packet['m'];P=z['P'];J=z['J'];u=packet['alpha']*z['x']+packet['beta']+1
    D=u+z['height_slack'];B=8*D
    E=[z[f'controller__edge_hat{i}']-1 for i in range(m)]
    S=[sum(E[e] for e,edge in enumerate(packet['edges']) if edge[2]==i+1) for i in range(8)]
    K8=sum(P**i for i in range(8));Kc=sum(P**i for i in range(m))
    Hb=sum(z[f'H{(i//2)^1}']*P**i for i in range(8))
    Mb=(B-1)*sum(S[i]*P**i for i in range(8))
    Zb=sum((z[f'Zhat{i}']-1)*P**i for i in range(8))
    Hc=sum(E[i]*P**i for i in range(m));Mc=J*Kc
    H0=Hb+P**8*Hc;M0=Mb+P**8*Mc;Z0=Zb+P**8*Hc
    Rb=(2*D-1)*J*K8;T=P**(m+8);T2=P**(m+16)
    H=H0+T*Hb+T2*B;M=M0+T*Rb+T2*(B-1);Z=Z0+T*Hb
    return dict(u=u,D=D,B=B,E=E,S=S,Hb=Hb,Mb=Mb,Zb=Zb,Hc=Hc,Mc=Mc,Rb=Rb,
                H0=H0,M0=M0,Z0=Z0,T=T,T2=T2,H=H,M=M,Z=Z,N=P**(m+18))


def manual(packet,z):
    v=data(packet,z);B,D,u,P=v['B'],v['D'],v['u'],z['P']
    initials=(D-1,D+u)*2;ends=(D,D+1)*2;answer=[]
    for i in range(4):
        dz=z[f'Zhat{2*i}']-z[f'Zhat{2*i+1}']
        ds=v['S'][2*i]-v['S'][2*i+1]
        answer.append(B*(z[f'H{i}']+dz-D*ds)-z[f'H{i}']-ends[i]*P+initials[i])
    answer.append(sum(z[f'H{i}'] for i in range(4))+z['history_bound']-P)
    native=shared.parent.selection.parent.native
    names=shared.parent.selection.parent.AUX
    scalar={name:z['selection__'+name] for name in names}
    scalar.update(q=16*v['N'],F3=16*v['Z']+8)
    nr=list(native.independent_sources(scalar))
    root=scalar['j']*scalar['c']-(2*scalar['r']+1)
    nr[12]+=nr[11]*(root*root-scalar['y_aux']**2)
    answer+=nr
    answer += [scalar['F1']+scalar['F3']-16*v['H']-12,
               scalar['F2']+scalar['F3']-16*v['M']-10,
               sum(z[f'Zhat{i}'] for i in range(8))+z['selection__bound_global']-P-1]
    answer += [(B-1)*z['J']+1-P,packet['m']+z['controller__radix_beta']-B,
               sum(v['E'])-z['J'],sum((a-B*b)*v['E'][i] for i,(a,b,_) in enumerate(packet['edges']))]
    assert len(answer)==26
    return answer


def audit():
    rng=random.Random(2618537);records=[];cases=0;t=sp.Symbol('t')
    for codes in ((),((1,2),),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
        packet=build(codes);sos,out=shared.polynomial_source(packet)
        m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']
        dm=packet['common_register_saving']['multiplications'];da=packet['common_register_saving']['additions_subtractions']
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
        assert counts=={'M':m+2*h+106+f['multiplications']-dm,'A':2*m+h+p+156+f['additions_subtractions']-da}
        assert len(sos)==3*m+3*h+p+262+f['operations']-3*min(h,3)
        for case in range(256):
            z={name:rng.randrange(1,14) if case<192 else rng.randrange(-6,7) for name in packet['parameters']+packet['auxiliaries']}
            env=shared.execute(sos,z);v=data(packet,z);rr=manual(packet,z)
            assert shared.residuals(packet,env)==rr and env[out]==sum(r*r for r in rr)
            for key in ('H','M','Z'):assert env['range_'+key]==v[key]
            assert env['range_total_scale']==v['N'] and env['range_cell']==2*v['D']-1
            if case<192:assert v['D']>=4 and env['selection__F3']>=8
            cases+=1
        names=packet['parameters']+packet['auxiliaries'];weights={name:1+i%3 for i,name in enumerate(names)}
        z={name:sp.Poly(weights[name]*t+i+1,t) for i,name in enumerate(names)}
        env=shared.execute(sos,z);s=weights
        top=s['selection__w']**2*s['selection__s']**4*s['selection__k']**2*(16*s['P']**(m+18))**6
        assert env[out].degree()==12*m+232 and env[out].LC()==top**2
        packet['sum_of_squares']=dict(operations=len(sos),multiplications=counts['M'],additions_subtractions=counts['A'],exact_degree=12*m+232,weighted_highest_coefficient=str(top**2),output=out)
        records.append(packet)
    return dict(packets=records,full_independent_residual_and_polynomial_assignments=cases,signed_assignments=cases//4)


def interface_checks():
    rng=random.Random(180026);pretyping=typed=0
    packet=build(((1,2),(3,4),(5,6)))
    for _ in range(512):
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(x=rng.randrange(1,5),height_slack=rng.randrange(1,12),J=rng.randrange(1,30))
        u=packet['alpha']*z['x']+packet['beta']+1;D=u+z['height_slack'];B=8*D;J=z['J'];P=(B-1)*J+1
        z['P']=P
        cuts=sorted([0,J]+[rng.randrange(J+1) for _ in range(packet['m']-1)])
        E=[cuts[i+1]-cuts[i] for i in range(packet['m'])]
        z.update({f'controller__edge_hat{i}':e+1 for i,e in enumerate(E)})
        z.update({f'H{i}':rng.randrange(1,P//5) for i in range(4)})
        z.update({f'Zhat{i}':rng.randrange((P-8)//8+1)+1 for i in range(8)})
        v=data(packet,z)
        assert all(0<=v[key]<P**8 for key in ('Hb','Mb','Zb','Rb'))
        assert 0<=v['Hc']<P**packet['m'] and 0<v['Mc']<P**packet['m']
        assert B<=P<P*P
        assert all(0<=v[key]<v['N'] for key in ('H','M','Z'))
        pretyping+=1
    for _ in range(512):
        D=1<<rng.randrange(2,7);B=8*D;t=rng.randrange(1,7);P=B**t;J=(P-1)//(B-1)
        m=packet['m'];edges=[rng.randrange(m) for _ in range(t)]
        E=[sum((e==i)*B**j for j,e in enumerate(edges)) for i in range(m)]
        S=[[int(packet['edges'][e][2]==i+1) for e in edges] for i in range(8)]
        rows=[[rng.randrange(2*D) for _ in range(4)] for _ in range(t)]
        for i in range(4):rows[0][i]=max(rows[0][i],1)
        H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
        Z=[sum(S[i][j]*rows[j][(i//2)^1]*B**j for j in range(t)) for i in range(8)]
        slots=(1,1,0,0,3,3,2,2);Hb=sum(H[slots[i]]*P**i for i in range(8));Mb=(B-1)*sum(sum(S[i][j]*B**j for j in range(t))*P**i for i in range(8));Zb=sum(Z[i]*P**i for i in range(8))
        Hc=sum(E[i]*P**i for i in range(m));Mc=J*sum(P**i for i in range(m));Rb=(2*D-1)*J*sum(P**i for i in range(8))
        T=P**(m+8);T2=T*P**8
        fullH=Hb+P**8*Hc+T*Hb+T2*B;fullM=Mb+P**8*Mc+T*Rb+T2*(B-1);fullZ=Zb+P**8*Hc+T*Hb
        assert fullH&fullM==fullZ and Hb&Rb==Hb and B&(B-1)==0
        assert sum(H)<P and P-sum(Z)-7>0
        typed+=1
    # With no cell activity, old selection alone does not bound an unselected history digit.
    D=4;B=8*D;P=B*B;J=1+B;bad_H=2*D
    assert bad_H & ((2*D-1)*J) != bad_H
    assert bad_H & 0 == 0
    # Dyadic P plus the repunit relation alone does not type the radix.
    B=56;P=2**20;J=(P-1)//(B-1)
    assert (B-1)*J+1==P and B&(B-1)!=0
    return dict(pretyping_region_bounds=pretyping,typed_joined_AND_fixtures=typed,
                omitted_range_fixture=dict(D=4,B=32,bad_low_digit=8),
                omitted_radix_fixture=dict(B=B,P=P,J=J))


def positive_outer_checks():
    code=physical.target_word(2);codes=(code,physical.inverse_word(code));packet=build(codes,1,1);records=[]
    for tokens in ((0,),(0,1,0)):
      for pad in (0,2):
        indices=[]
        for token in tokens:
            start=1+sum(len(c) for c in codes[:token]);indices+=list(range(start,start+len(codes[token])))
        indices += [0]*pad;word=[packet['edges'][i][2] for i in indices];u=3
        state=[-1,u,-1,u];signed=[state[:]]
        for label in word:
            if label:
                i=(label-1)//2;state[i]+=(1 if label%2 else -1)*state[i^1]
            signed.append(state[:])
        assert state==[0,1,0,1]
        limit=max(u,packet['m']//8,max(abs(v) for row in signed for v in row));D=1<<limit.bit_length()
        B=8*D;t=len(word);P=B**t;J=(P-1)//(B-1)
        rows=[[D+v for v in row] for row in signed[:-1]]
        assert all(0<v<2*D for row in rows for v in row)
        H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
        Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
        E=[sum((e==i)*B**j for j,e in enumerate(indices)) for i in range(packet['m'])]
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(height_slack=D-u,P=P,J=J,history_bound=P-sum(H))
        z.update({f'H{i}':h for i,h in enumerate(H)});z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        z.update({f'controller__edge_hat{i}':e+1 for i,e in enumerate(E)})
        z['selection__bound_global']=P-sum(Z)-7;z['controller__radix_beta']=B-packet['m']
        v=data(packet,z);assert v['H']&v['M']==v['Z']
        fields=shared.parent.selection.parent.truth_fields(v['N'],v['H'],v['M'])
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        assert min(z.values())>0
        env=shared.execute(packet['source'],z);rr=shared.residuals(packet,env)
        assert rr[:5]==[0]*5 and rr[6]==0 and rr[19:]==[0]*7
        records.append(dict(duration=t,D=D,radix=B,height_slack=D-u,P_bits=P.bit_length(),shared_outer_comparisons_verified=True))
    return dict(fixtures=records,scope='The one remaining native core contains placeholders; its full positive extension follows from the exact AND theorem.')


def verify():
    return dict(status='PASS_GROUP_RANGE_PROJECTIVE_COMPILER',source=audit(),interfaces=interface_checks(),positive_outer=positive_outer_checks(),
                certificate_operations='3m+3h+p+185+f_flow-3min(h,3)',polynomial_operations='3m+3h+p+262+f_flow-3min(h,3)',
                equations=26,positive_witnesses='m+40',exact_degree='12m+232',
                generic_relation='Paired matrix action on(-1,u), ending at(e2,e2), u=alpha*x+beta+1.',
                universality='Requires the separate special-subgroup lower-projective theorem; no numerical universal table is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
