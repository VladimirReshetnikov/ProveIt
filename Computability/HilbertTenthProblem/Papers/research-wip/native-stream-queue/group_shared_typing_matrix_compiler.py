"""Share one positive AND kernel between regular control and eight selections.

The47-comparison certificate costs7m+3h+p+223 before optional subsequent
controller optimizations. Its full positive theorem is proved in the note;
finite outer fixtures do not assert astronomical Pell core zeros.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_complete_matrix_compiler as parent


def build(codes, alpha=24, beta=12):
    old = parent.build(codes, alpha, beta)
    parts = {}
    for block in old['blocks']:
        start, length = block['instruction_start'], block['instruction_count']
        parts[block['name']] = old['source'][start:start+length]
    ctrl = parts['controller']
    begin = next(i for i, gate in enumerate(ctrl) if gate[0] == 'controller__edge_word8')
    end = next(i for i, gate in enumerate(ctrl) if gate[0] == 'controller__source_weighted0')
    removed = ctrl[begin:end]
    assert len(removed) == 57
    assert Counter('M' if op == '*' else 'A' for _,op,_,_ in removed) == {'M':30, 'A':27}
    previous_power = 'P' if old['h'] == 1 else f"controller__lane_power{old['h']-1}"
    added = [
        ('joint_Pm', '*', previous_power, previous_power),
        ('joint_scale', '*', 'selection__P8', 'joint_Pm'),
        ('joint_edge_shift', '*', 'selection__P8', 'controller__edge_word'),
        ('joint_mask_shift', '*', 'selection__P8', 'controller__origin_mask'),
        ('joint_H', '+', 'selection__Hbatch', 'joint_edge_shift'),
        ('joint_M', '+', 'selection__Mbatch', 'joint_mask_shift'),
        ('joint_Z', '+', 'selection__Zbatch', 'joint_edge_shift'),
    ]
    replacements = {
        'selection__q': ('*',16,'joint_scale'),
        'selection__scaled_A': ('*',16,'joint_H'),
        'selection__scaled_B': ('*',16,'joint_M'),
        'selection__scaled_Z': ('*',16,'joint_Z'),
    }
    selector = []
    for gate in parts['selection']:
        name = gate[0]
        if name == 'selection__q':
            selector += added
        selector.append((name, *replacements[name]) if name in replacements else gate)
    source = parts['history']+ctrl[:begin]+selector+ctrl[end:]+parts['geometry']
    # Keep the parent's comparison order after deleting the13 subset comparisons.
    pairs = old['comparisons'][:25]+old['comparisons'][38:]
    deleted_aux = {f'controller__{name}' for name in
                   ['F0']+parent.control.binary.CORE_NAMES+['odd_half','bound_beta']}
    assert len(deleted_aux) == 20
    aux = [name for name in old['auxiliaries'] if name not in deleted_aux]
    assert len(old['auxiliaries'])-len(aux) == 20
    m,h,p = old['m'],old['h'],old['projection_additions']
    counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in source)
    assert counts == {'M':3*m+2*h+102,'A':4*m+h+p+121}
    assert len(source) == 7*m+3*h+p+223 and len(pairs) == 47 and len(aux) == m+67
    available = {'x', *aux}
    for name,op,left,right in source:
        assert name not in available and op in ('+','-','*')
        assert all(isinstance(v,int) or v in available for v in (left,right))
        available.add(name)
    assert all(isinstance(v,int) or v in available for pair in pairs for v in pair)
    return dict(codes=old['codes'], edges=old['edges'], alpha=alpha,beta=beta,m=m,h=h,
                projection_additions=p,parameters=['x'],auxiliaries=aux,source=source,
                comparisons=pairs,operations=len(source),multiplications=counts['M'],
                additions_subtractions=counts['A'],equations=47,positive_witnesses=len(aux),
                added_source=added,removed_source=removed,
                removed_positive_coordinates=sorted(deleted_aux),
                changed_registers=list(replacements))


def execute(source, values):
    return parent.execute(source, values)


def residuals(packet, env):
    return parent.residuals(packet, env)


def polynomial_source(packet):
    return parent.polynomial_source(packet)


def joint_values(packet, z):
    P=z['P'];q=z['q_geom'];B=8*q*q;J=z['J'];m=packet['m']
    E=[z[f'controller__edge_hat{i}']-1 for i in range(m)]
    Hc=sum(E[i]*P**i for i in range(m))
    Mc=J*sum(P**i for i in range(m))
    slots=(1,1,0,0,3,3,2,2)
    Hb=sum(z[f'H{slots[i]}']*P**i for i in range(8))
    Mb=(B-1)*sum((z[f'Shat{i}']-1)*P**i for i in range(8))
    Zb=sum((z[f'Zhat{i}']-1)*P**i for i in range(8))
    return dict(B=B,E=E,Hc=Hc,Mc=Mc,Hb=Hb,Mb=Mb,Zb=Zb,
                H=Hb+P**8*Hc,M=Mb+P**8*Mc,Z=Zb+P**8*Hc,N=P**(m+8))


def manual_residuals(packet,z):
    data=joint_values(packet,z);B=data['B'];P=z['P'];q=z['q_geom'];D=q*q
    r=packet['alpha']*z['x']+packet['beta']
    starts=(D+q,D+1)*2;ends=(D+(1+r)*q+1,D-r*r*q+1-r)*2
    answer=[]
    for i in range(4):
        dz=z[f'Zhat{2*i}']-z[f'Zhat{2*i+1}']
        ds=z[f'Shat{2*i}']-z[f'Shat{2*i+1}']
        answer.append(B*(z[f'H{i}']+dz-D*ds)-z[f'H{i}']-ends[i]*P+starts[i])
    answer.append(sum(z[f'H{i}'] for i in range(4))+z['history_bound']-P)
    native=parent.selection.parent.native
    names=parent.selection.parent.AUX
    scalar={name:z[f'selection__{name}'] for name in names}
    scalar.update(q=16*data['N'],F3=16*data['Z']+8)
    nr=list(native.independent_sources(scalar))
    u=scalar['j']*scalar['c']-(2*scalar['r']+1)
    nr[12]+=nr[11]*(u*u-scalar['y_aux']**2)
    answer+=nr
    answer += [scalar['F1']+scalar['F3']-16*data['H']-12,
               scalar['F2']+scalar['F3']-16*data['M']-10,
               sum(z[f'Zhat{i}'] for i in range(8))+z['selection__bound_global']-P-1]
    E=data['E'];edges=packet['edges'];m=packet['m']
    answer += [(B-1)*z['J']+1-P,m+z['controller__radix_beta']-B,sum(E)-z['J'],
               sum((s-B*t)*E[i] for i,(s,t,_) in enumerate(edges))]
    answer += [1+sum(E[i] for i,e in enumerate(edges) if e[2]==label)-z[f'Shat{label-1}']
               for label in range(1,9)]
    gp=parent.geometry.build(shared_B=True)
    gz={name:z[f'geometry__{name}'] for name in gp['auxiliaries']}
    gz.update(q=q,B=B,J=z['J'])
    answer += parent.geometry.manual(gz,B)
    assert len(answer)==47
    return answer


def source_checks():
    rng=random.Random(2234767);records=[];cases=0
    for codes in ((),((1,),(2,)),((1,3),(4,2)),((1,3),(4,2),(5,7,6,8))):
        packet=build(codes);sos,out=polynomial_source(packet)
        m,h,p=packet['m'],packet['h'],packet['projection_additions']
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
        assert len(sos)==7*m+3*h+p+363
        assert counts=={'M':3*m+2*h+149,'A':4*m+h+p+214}
        for case in range(256):
            z={name:rng.randrange(1,12) if case<192 else rng.randrange(-5,6)
               for name in packet['parameters']+packet['auxiliaries']}
            env=execute(sos,z);rr=manual_residuals(packet,z);data=joint_values(packet,z)
            assert residuals(packet,env)==rr and env[out]==sum(v*v for v in rr)
            for key in ('H','M','Z'):
                assert env[f'joint_{key}']==data[key]
            assert env['joint_scale']==data['N']
            if case<192:assert data['Hc']>=0 and data['Z']>=0 and env['selection__F3']>=8
            cases+=1
        packet['sum_of_squares']=dict(operations=len(sos),multiplications=counts['M'],
                                      additions_subtractions=counts['A'],output=out)
        records.append(packet)
    return dict(packets=records,full_manual_residual_and_SOS_assignments=cases,
                signed_assignments=256)


def degree_checks():
    t=sp.Symbol('t');records=[]
    for codes in ((),((1,),(2,)),((1,3),(4,2)),((1,3),(4,2),(5,7,6,8))):
        packet=build(codes);names=packet['parameters']+packet['auxiliaries']
        degrees={name:1 for name in names}
        def deg(value):return 0 if isinstance(value,int) else degrees[value]
        for name,op,left,right in packet['source']:
            degrees[name]=deg(left)+deg(right) if op=='*' else max(deg(left),deg(right))
        upper=[max(deg(a),deg(b)) for a,b in packet['comparisons']]
        top_degree=6*packet['m']+56
        assert upper[9]==top_degree and all(d<top_degree for i,d in enumerate(upper) if i!=9)
        scales={name:1+i%3 for i,name in enumerate(names)}
        z={name:sp.Poly(scales[name]*t+i+1,t) for i,name in enumerate(names)}
        sos,out=polynomial_source(packet);env=execute(sos,z)
        first=env[packet['comparisons'][9][0]]-env[packet['comparisons'][9][1]]
        s=scales
        highest=s['selection__w']**2*s['selection__s']**4*s['selection__k']**2*(16*s['P']**(packet['m']+8))**6
        assert first.degree()==top_degree and first.LC()==highest
        assert env[out].degree()==12*packet['m']+112 and env[out].LC()==highest**2
        records.append(dict(m=packet['m'],residual_degree_bounds=upper,
                            exact_polynomial_degree=12*packet['m']+112,
                            weighted_highest_coefficient=str(highest**2)))
    return records


def interface_checks():
    rng=random.Random(223000);untyped=typed=0
    # Check algebraic low-lane bounds before any Boolean edge assumption.
    for _ in range(1024):
        codes=tuple(tuple(rng.randrange(1,9) for _ in range(rng.randrange(1,5)))
                    for _ in range(rng.randrange(1,5)))
        packet=build(codes);m=packet['m'];bits=max(4,m.bit_length());B=1<<bits
        t=rng.randrange(2,5);P=B**t;J=(P-1)//(B-1)
        cuts=sorted([0,J]+[rng.randrange(J+1) for _ in range(m-1)])
        E=[cuts[i+1]-cuts[i] for i in range(m)]
        rng.shuffle(E)
        S=[sum(E[i] for i,e in enumerate(packet['edges']) if e[2]==a) for a in range(1,9)]
        Hc=sum(E[i]*P**i for i in range(m));Mc=J*sum(P**i for i in range(m))
        Mb=(B-1)*sum(S[i]*P**i for i in range(8))
        assert all(0<=e<=J for e in E) and all(0<=s<=J for s in S)
        assert 0<=Hc<P**m and 0<=Mc<P**m and 0<=Mb<P**8
        untyped+=1
    # Low canonical digits may vanish or exceed the eventual history margin.
    for _ in range(1024):
        bits=rng.randrange(4,7);B=1<<bits;t=rng.randrange(2,5);P=B**t
        m=1<<rng.randrange(1,4);J=(P-1)//(B-1)
        labels=[rng.randrange(m) for _ in range(t)]
        E=[sum((label==i)*B**j for j,label in enumerate(labels)) for i in range(m)]
        Hc=sum(E[i]*P**i for i in range(m));Mc=J*sum(P**i for i in range(m))
        assert Hc&Mc==Hc
        Hb=rng.randrange(P**8);Mb=rng.randrange(P**8);Zb=Hb&Mb
        H=Hb+P**8*Hc;M=Mb+P**8*Mc;Z=Zb+P**8*Hc
        assert H&M==Z
        fields=parent.selection.parent.truth_fields(P**(m+8),H,M)
        assert all(v>0 for v in fields) and fields[3]==16*Z+8
        assert sum(fields)==16*P**(m+8)-1
        typed+=1
    # Carry contamination really can fake the upper subset without the low bound.
    N=16;Hc=1;Mc=0;Hb=Zb=0;Mb=N
    assert (Hb+N*Hc)&(Mb+N*Mc)==Zb+N*Hc and Hc&Mc!=Hc
    return dict(pretyping_bound_cases=untyped,joined_truth_partition_cases=typed,
                omitted_low_mask_bound_counterexample=dict(N=N,Hc=Hc,Mc=Mc,Hb=Hb,Mb=Mb,Zb=Zb))



def positive_outer_checks():
    physical=parent.physical
    code=physical.target_word(2);codes=(code,physical.inverse_word(code))
    packet=build(codes,alpha=1,beta=1);records=[]
    for tokens in ((0,),(0,1,0)):
      for padding in (0,2):
        indices=[]
        for token in tokens:
            start=1+sum(len(c) for c in codes[:token])
            indices.extend(range(start,start+len(codes[token])))
        indices += [0]*padding
        word=tuple(packet['edges'][i][2] for i in indices)
        assert parent.control.action_path(packet['edges'],indices)
        t=len(word);q=2**t;B=8*q*q;P=B**t;J=(P-1)//(B-1)
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(q_geom=q,P=P,J=J)
        current=[q,1,q,1];rows=[]
        for label in word:
            rows.append([q*q+v for v in current])
            if label:
                target=(label-1)//2
                current[target]+=(1 if label%2 else -1)*current[target^1]
        assert current==[3*q+1,-4*q-1]*2
        H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
        S=[sum((label==i+1)*B**j for j,label in enumerate(word)) for i in range(8)]
        Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
        E=[sum((e==i)*B**j for j,e in enumerate(indices)) for i in range(packet['m'])]
        z.update({f'H{i}':v for i,v in enumerate(H)})
        z.update({f'Shat{i}':v+1 for i,v in enumerate(S)})
        z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
        z['history_bound']=P-sum(H)
        z['selection__bound_global']=P-sum(Z)-7
        z['controller__radix_beta']=B-packet['m']
        data=joint_values(packet,z)
        assert data['H']&data['M']==data['Z']
        fields=parent.selection.parent.truth_fields(data['N'],data['H'],data['M'])
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        z['geometry__s']=3;z['geometry__w']=J//q+1
        z['geometry__bound_beta']=q*z['geometry__w']-J
        z['geometry__index_beta']=J-B
        assert min(z.values())>0 and J.bit_count()==t
        env=execute(packet['source'],z);rr=residuals(packet,env)
        assert rr[:5]==[0]*5 and rr[6]==0 and rr[19:34]==[0]*15 and rr[-3:]==[0]*3
        assert env['selection__F3']==fields[3] and env['selection__q']==16*data['N']
        assert physical.word_matrices(word)==(physical.target(2),)*2
        records.append(dict(duration=t,table_edges=packet['m'],P_bits=P.bit_length(),
                            joint_scale_bits=data['N'].bit_length(),common_outer_equations=True,
                            all_supplied_coordinates_positive=True))
    return dict(fixtures=records,scope='Full accepted-word common-interface checks; both native cores retain placeholders. The parametric proof supplies their simultaneous positive extensions.')


def verify():
    return dict(status='PASS_GROUP_SHARED_TYPING_MATRIX_COMPILER',source=source_checks(),
                degrees=degree_checks(),interfaces=interface_checks(),positive_outer=positive_outer_checks(),
                certificate_operations='7m+3h+p+223',polynomial_operations='7m+3h+p+363',
                positive_witnesses='m+67',equations=47,exact_degree='12m+112',
                scope='Complete fixed-table ordinary-input theorem; universal alphabet is not numerically instantiated.',
                evidence_limit='Finite outer partitions are not full Pell zeros; their positive extensions are supplied by the parametric theorem.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
