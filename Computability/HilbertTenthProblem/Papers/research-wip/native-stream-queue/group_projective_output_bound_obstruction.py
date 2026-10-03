"""Dropping the global output bound admits a false endpoint on an empty table.

All remaining outer equations and the exact scalar AND hold. The positive
native extension is supplied parametrically, not numerically expanded.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_padded_program_margin as parent

execute=parent.execute
residuals=parent.residuals
polynomial_source=parent.polynomial_source
scalar_parent=parent.parent
unit_parent=scalar_parent.parent
boundary=unit_parent.parent

CODES=tuple((i,) for i in range(3,9))


def relaxed_build(alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    old=parent.build(CODES,alpha,beta,variant,controller_mask,compute_length)
    pair=next(pair for pair in old['comparisons'] if pair[0]=='selection__Zglobal')
    index=old['comparisons'].index(pair)
    assert ('selection__Zglobal','+','selection__Zsum7','selection__bound_global') in old['source']
    source=[(name,'-',pair[1],'selection__Zsum7') if name=='selection__Zglobal' else (name,op,a,b)
            for name,op,a,b in old['source']]
    assert sum('selection__bound_global' in (a,b) for _,_,a,b in old['source'])==1
    new=dict(old)
    new.update(source=source,comparisons=[pair for i,pair in enumerate(old['comparisons']) if i!=index],
               auxiliaries=[name for name in old['auxiliaries'] if name!='selection__bound_global'],
               equations=old['equations']-1,positive_witnesses=old['positive_witnesses']-1,
               dropped_bound_index=index,computed_output_slack='selection__Zglobal')
    return new


def witness_outer(alpha,beta,x):
    u=alpha*x+beta+1
    assert alpha+beta+1>=8 and x>0
    word=(8,)*(u-1)+(6,)+(4,)*u
    states=boundary.trace(word,u)
    assert states[-1]==[1,0,0,1]
    assert all(row[0]==1 for row in states)
    D=1<<(u+1).bit_length();shift=D-1;B=8*D;t=len(word)
    assert D>u+1 and t==2*u
    P=B**t;J=(P-1)//(B-1);omega=P//B;G=omega*P*(P-1)
    rows=[[shift+v for v in row] for row in states[:-1]]
    assert all(0<v<2*D for row in rows for v in row)
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    true_Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    assert true_Z[:3]==[0,0,0]
    assert true_Z[3]==D*B**u*(B**u-1)//(B-1)>omega
    assert true_Z[5]==D*B**(u-1)
    assert true_Z[7]==D*(B**(u-1)-1)//(B-1)
    false_Z=list(true_Z)
    false_Z[:4]=[G,G+omega,0,true_Z[3]-omega]
    assert min(false_Z)>=0
    packed=lambda Z:sum(z*P**i for i,z in enumerate(Z))
    assert packed(false_Z)==packed(true_Z)
    assert [false_Z[2*i]-false_Z[2*i+1]-(true_Z[2*i]-true_Z[2*i+1]) for i in range(4)]==[-omega,omega,0,0]
    old_bound=P-7-sum(true_Z);new_bound=P-7-sum(false_Z)
    assert old_bound>0 and new_bound==old_bound-2*G<0
    return dict(u=u,word=word,states=states,D=D,B=B,P=P,J=J,omega=omega,G=G,
                H=H,true_Z=true_Z,false_Z=false_Z,true_output_slack=old_bound,
                false_output_slack=new_bound,history_bound=P-sum(H))


def outer_checks():
    records=[]
    for alpha,beta,x in ((1,6,1),(24,12,1),(24,12,2)):
      v=witness_outer(alpha,beta,x)
      for variant in ('four','six'):
       for reuse in (False,True):
        for comp in (False,True):
            new=relaxed_build(alpha,beta,variant,reuse,comp)
            old=parent.build(CODES,alpha,beta,variant,reuse,comp)
            assert new['m']==8
            labels={label:i for i,(_,_,label) in enumerate(new['edges']) if label}
            E=[sum((labels[label]==i)*v['B']**j for j,label in enumerate(v['word'])) for i in range(8)]
            z={name:1 for name in new['parameters']+new['auxiliaries']}
            z.update(x=x,height_slack=v['D']-v['u'],history_bound=v['history_bound'])
            if not comp:z['P']=v['P']
            z.update({f'H{i}':H for i,H in enumerate(v['H'])})
            z.update({f'controller__edge_hat{i}':e+1 for i,e in enumerate(E)})
            z.update({f'Zhat{i}':Z+1 for i,Z in enumerate(v['false_Z'])})
            data=unit_parent.region_data(new,dict(z,P=v['P'],J=v['J']))
            assert data['H']&data['M']==data['Z'] and 0<=data['H']<data['N'] and 0<=data['M']<data['N']
            fields=unit_parent.range_parent.shared.parent.selection.parent.truth_fields(data['N'],data['H'],data['M'])
            z.update({f'selection__F{i}':fields[i] for i in range(3)})
            assert min(z.values())>0
            env=execute(new['source'],z);rr=residuals(new,env)
            assert env['selection__Zglobal']==v['false_output_slack']<0
            assert rr[:5]==[0]*5 and rr[-1]==0
            assert env['computed_J']==v['J'] and env['controller__geometry_power']==v['P']
            assert env['selection__bs_q']==1
            for left,right in new['comparisons']:
                if left in ('selection__input_A','selection__input_B','controller__geometry_power'):
                    assert env[left]==env[right]
            reference=dict(z,selection__bound_global=v['true_output_slack'])
            reference.update({f'Zhat{i}':Z+1 for i,Z in enumerate(v['true_Z'])})
            before=execute(old['source'],reference);before_rr=residuals(old,before)
            assert before_rr[:4]==[v['P'],-v['P'],0,0]
            assert before_rr[old['comparisons'].index(('selection__Zglobal',next(r for l,r in old['comparisons'] if l=='selection__Zglobal')))]==0
            assert rr[4:]==[r for i,r in enumerate(before_rr) if i>=4 and i!=new['dropped_bound_index']]
            for name in ('range_H','range_M','range_Z','selection__q','selection__F3','selection__bs_packed','unit_product'):
                assert env[name]==before[name]
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in new['source'])
            assert counts=={'M':old['multiplications'],'A':old['additions_subtractions']}
            assert len(polynomial_source(new)[0])==len(polynomial_source(old)[0])-3
            records.append(dict(alpha=alpha,beta=beta,x=x,u=v['u'],m=8,D=v['D'],duration=len(v['word']),
                variant=variant,controller_mask=reuse,compute_length=comp,P_bits=v['P'].bit_length(),
                certificate_operations=new['operations'],equations=new['equations'],
                positive_witnesses=new['positive_witnesses'],polynomial_operations=len(polynomial_source(new)[0]),
                true_endpoint=v['states'][-1],claimed_endpoint=[0,1,0,1],
                all_supplied_coordinates_positive=True,all_non_native_residuals_zero=True,
                exact_AND_and_native_checksum=True,computed_output_slack_negative=True,
                native_residuals_unchanged_from_exact_AND_projection=True))
    return dict(fixtures=records,scope='Native coordinates are placeholders; their positive extension follows from the exact scalar AND theorem at the unchanged fields and scale.')


def residual_response_checks():
    rng=random.Random(802403);cases=0
    for variant in ('four','six'):
      for reuse in (False,True):
       for comp in (False,True):
        packet=relaxed_build(variant=variant,controller_mask=reuse,compute_length=comp)
        sos,out=polynomial_source(packet)
        for case in range(64):
            z={name:rng.randrange(1,8) if case<48 else rng.randrange(-5,6)
               for name in packet['parameters']+packet['auxiliaries']}
            before=execute(sos,z);P=before['controller__geometry_power'] if comp else z['P']
            omega=rng.randrange(1,7);G=omega*P*(P-1)
            changed=dict(z)
            changed['Zhat0']+=G;changed['Zhat1']+=G+omega;changed['Zhat3']-=omega
            env=execute(sos,changed);rr=residuals(packet,env);oldrr=residuals(packet,before)
            expected=list(oldrr);expected[0]-=before['B']*omega;expected[1]+=before['B']*omega
            assert rr==expected
            assert env[out]==sum(r*r for r in expected)
            assert env['selection__Zglobal']==before['selection__Zglobal']-2*G
            for name in ('selection__Zbatch','range_Z','selection__F3','selection__bs_packed','unit_product'):
                assert env[name]==before[name]
            cases+=1
    return dict(full_remaining_residual_and_SOS_response_cases=cases,signed_cases=cases//4)


def empty_table_checks():
    # Every first block is lower triangular unipotent, hence fixes first coordinates.
    matrices=boundary.physical.word_matrices
    for code in CODES:
        first,_=matrices(code)
        assert first[:2]==(1,0) and first[3]==1
    rng=random.Random(831)
    for _ in range(256):
        word=tuple(rng.choice(range(3,9)) for _ in range(rng.randrange(80)))
        first,_=matrices(word)
        assert first[:2]==(1,0) and first[3]==1
        u=rng.randrange(8,90)
        assert boundary.physical.action(first,(1,u))[0]==1
    return dict(fixed_codes=[list(c) for c in CODES],word_checks=256,
                invariant='First block always[[1,0],[n,1]], so first coordinate stays1 and can never equal e2 first coordinate0.')


def verify():
    return dict(status='PASS_OUTPUT_BOUND_DELETION_FALSE_ENDPOINT',outer=outer_checks(),
                exact_perturbation=residual_response_checks(),empty_language=empty_table_checks(),
                one_rejected_source=relaxed_build(controller_mask=True,compute_length=True),
                unchanged_globals='All histories, selectors, B/P/J, joined H/M/Z, native inputs and ordinary x.',
                exact_projection='For this fixed table and any positive alpha,beta with alpha+beta+1>=8, the full relaxed compiler accepts every positive input; the genuine paired-action language is empty.',
                restriction='This refutes the uniform deletion theorem. It does not independently classify deletion for the special uninstantiated universal subgroup alphabet.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
