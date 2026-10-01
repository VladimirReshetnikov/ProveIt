"""Large fixed program numerals make the separate table-height add redundant.

No runtime padding or input recoding is introduced. The condition is a
compile-time inequality and the full degree proof is constant translation.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_scalar_projections as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    old=parent.build(codes,alpha,beta,variant,controller_mask,compute_length)
    assert alpha+beta+1>=old['m'],'fixed input numerals must supply the table margin'
    assert ('height_sum','+','history__u','height_slack') in old['source']
    assert ('D','+','height_sum',old['m']) in old['source']
    source=[(name,'+','history__u','height_slack') if name=='D' else (name,op,a,b)
            for name,op,a,b in old['source'] if name!='height_sum']
    available={'x',*old['auxiliaries']}
    for name,op,a,b in source:
        assert name not in available and op in ('+','-','*')
        assert all(isinstance(v,int) or v in available for v in (a,b))
        available.add(name)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications'],'A':old['additions_subtractions']-1}
    packet=dict(old)
    packet.update(source=source,operations=len(source),additions_subtractions=counts['A'],
                  expanded_height='D=u+height_slack',
                  compile_time_margin=dict(minimal_u=alpha+beta+1,padded_edges=old['m']),
                  boundary_source=[row for row in source if row[0] in ('history__input_product','history__u','D','history__c0','history__d0')])
    assert len(source)==old['operations']-1
    return packet


def general_coordinates(packet,z):
    return dict(z,height_slack=z['height_slack']-packet['m'])


def source_checks():
    rng=random.Random(1853736);records=[];cases=nonpositive_restored=0
    tables=((),((1,2),(3,4)),tuple((i,) for i in range(1,9)))
    for codes in tables:
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            new=build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            old_sos,old_out=polynomial_source(old);sos,out=polynomial_source(new)
            assert new['comparisons']==old['comparisons'] and new['auxiliaries']==old['auxiliaries']
            assert len(sos)==len(old_sos)-1
            for case in range(128):
                z={name:rng.randrange(1,13) if case<96 else rng.randrange(-6,7)
                   for name in new['parameters']+new['auxiliaries']}
                env=execute(sos,z);restored=general_coordinates(new,z)
                before=execute(old_sos,restored)
                assert all(env[name]==before[name] for name,_,_,_ in new['source'])
                rr=residuals(new,env)
                assert rr==residuals(old,before) and env[out]==before[old_out]==sum(r*r for r in rr)
                if case<96:
                    assert env['D']>env['history__u']>=new['m'] and env['B']>new['m']
                    assert env['computed_J']>=0
                    if restored['height_slack']<=0:nonpositive_restored+=1
                cases+=1
            weights={name:1+i%3 for i,name in enumerate(new['parameters']+new['auxiliaries'])}
            degree,_=parent.degree_top(new,weights)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            new['sum_of_squares']=dict(operations=len(sos),multiplications=counts['M'],
                additions_subtractions=counts['A'],exact_degree=degree,
                degree_argument='Identical polynomial under height_slack -> height_slack-m; translation preserves the full highest homogeneous part.',output=out)
            records.append(new)
    # The specialization must reject a table whose actual margin is too small.
    try:build(tuple((i,) for i in range(1,9)),alpha=1,beta=1)
    except AssertionError as exc:assert 'fixed input numerals' in str(exc)
    else:raise AssertionError('unpaid table margin accepted')
    return dict(packets=records,complete_source_residual_and_SOS_identities=cases,
                positive_assignments=3*cases//4,signed_assignments=cases//4,
                positive_tuples_with_nonpositive_general_height=nonpositive_restored,
                invalid_compile_time_margin_rejected=True)


def valuation(n):
    assert n>0
    return (n & -n).bit_length()-1


def enumeration_checks():
    cases=0
    for e in range(20):
      for m in (2,4,8,16,32,127,1024):
        p=(1<<e)*(2*m+1)-1
        assert valuation(p+1)==e and p>=2*m
        # alpha=12*2^(p+1) exceeds p+1, so no enormous numeral is materialized.
        assert p+1>m
        cases+=1
    fibres=0
    for e in range(12):
      for k in range(48):
        p=(1<<e)*(2*k+1)-1
        assert valuation(p+1)==e
        for x in (1,2,17):
            encoded=(1<<p)*(2*x+1)
            assert valuation(encoded)==p and ((encoded>>p)-1)//2==x
        fibres+=1
    return dict(table_dependent_padded_indices=cases,infinite_fibre_pattern_cases=fibres,
                theorem='S_p=T_v2(p+1); choosing p=2^e(2m+1)-1 after the fixed alphabet exists preserves T_e and gives the fixed-numeral margin.')


def positive_outer_checks():
    physical=parent.parent.parent.physical
    codes=tuple((i,) for i in range(1,9))
    word=parent.parent.parent.reflect_codes((physical.target_word(36),))[0]+(0,0)
    states=parent.parent.parent.trace(word,37)
    assert states[-1]==[0,1,0,1]
    limit=max(37,1+max(abs(v) for row in states for v in row));D=1<<limit.bit_length()
    B=8*D;duration=len(word);P=B**duration;J=(P-1)//(B-1);shift=D-1
    rows=[[shift+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    E=[sum((label==i)*B**j for j,label in enumerate(word)) for i in range(16)]
    records=[]
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        packet=build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
        assert packet['m']==16
        assert [edge[2] for edge in packet['edges'][:9]]==list(range(9))
        z={name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(height_slack=D-37,history_bound=P-sum(H))
        if not comp:z['P']=P
        z.update({f'H{i}':v for i,v in enumerate(H)})
        z.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        z.update({f'controller__edge_hat{i}':v+1 for i,v in enumerate(E)})
        z['selection__bound_global']=P-sum(Z)-7
        restored=dict(z,P=P,J=J)
        v=parent.parent.region_data(packet,restored)
        assert v['H']&v['M']==v['Z']
        fields=parent.parent.range_parent.shared.parent.selection.parent.truth_fields(v['N'],v['H'],v['M'])
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        assert min(z.values())>0
        env=execute(packet['source'],z);rr=residuals(packet,env)
        assert env['D']==D and env['computed_J']==J and env['controller__geometry_power']==P
        assert rr[:5]==[0]*5 and rr[-1]==0
        for left,right in packet['comparisons']:
            if left in ('selection__input_A','selection__input_B','selection__Zglobal','controller__geometry_power'):
                assert env[left]==env[right]
        for key in ('H','M','Z'):assert env['range_'+key]==v[key]
        assert env['selection__bs_q']==1
        records.append(dict(variant=variant,controller_mask=reuse,compute_length=comp,
                            m=16,minimal_u=37,D=D,duration=duration,all_outer_fields_positive=True))
    return dict(fixtures=records,scope='Only native Pell coordinates remain placeholders; their exact positive extension is supplied by the theorem, not these finite checks.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_PADDED_PROGRAM_MARGIN',source=source_checks(),
                padded_enumeration=enumeration_checks(),positive_outer=positive_outer_checks(),
                certificate_operations='3m+3h+p+185+f_flow-3min(h,3)-controller_mask',
                source_saving=dict(multiplications=0,additions_subtractions=1),
                domain='Fixed positive alpha,beta with alpha+beta+1>=m; x and every existential coordinate remain strictly positive.',
                universal_scope='A fixed alphabet built from the explicitly padded enumeration, not an assertion about the earlier unspecified enumeration.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
