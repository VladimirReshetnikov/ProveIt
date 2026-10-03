"""Type the group compiler radix through a product native scale, saving one M.

Only the canonical joint-unit fixed-table compiler is supported.  Its
numerical universal alphabet remains uninstantiated.  Native witnesses
are reconstructed; no same-positive-tuple theorem is claimed.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import group_projective_label_aligned_lanes as parent

DEFAULT_CODES=((1,2,3,4,5,6,7,8,1,2),)
execute,residuals=parent.execute,parent.residuals
polynomial_source=parent.polynomial_source
FACTORS=('first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit')


def ancestors(source,roots):
    nodes={n:(a,b) for n,_,a,b in source};needed=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in nodes and n not in needed:
            needed.add(n);pending.extend(nodes[n])
    return needed


def sort_source(source,inputs):
    remaining=list(source);result=[];known=set(inputs)
    while remaining:
        rest=[]
        for row in remaining:
            n,op,a,b=row
            if all(not isinstance(v,str) or v in known for v in (a,b)):
                assert n not in known and op in ('+','-','*')
                result.append(row);known.add(n)
            else:rest.append(row)
        assert len(rest)<len(remaining),'missing dependency or cycle'
        remaining=rest
    return result


def rewrite(old):
    assert old.get('joint_bound_unit_merged') and not old.get('product_radix_scale')
    assert old==parent.build(old['codes'],old['alpha'],old['beta'],'joint',old['controller_mask'],old['compute_length']),'complete canonical label-aligned joint packet required'
    assert old['active_edges']>1,'nonempty physical macro table required'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows['B']==('*',16,'D')
    assert rows['range_Bshift']==('*','range_body_scale','B')
    assert rows['range_Bminus_shift']==('*','range_body_scale','controller__cell_minus1')
    assert rows['range_total_scale'][0:2]==('*','range_body_scale')
    assert rows['selection__q']==('*',16,'range_total_scale')
    assert {n for n,_,a,b in old['source'] if 'range_total_scale' in (a,b)}=={'selection__q'}
    assert not any('range_total_scale' in pair for pair in old['comparisons'])
    P='controller__geometry_power' if old['compute_length'] else 'P'
    powers={P:1}
    for n,op,a,b in old['source']:
        if op=='*' and a in powers and b in powers:powers[n]=powers[a]+powers[b]
    a=powers['range_body_scale']
    assert a==old['scale_exponent']-2 and powers[rows['range_total_scale'][2]]==2
    source=[]
    for n,op,x,y in old['source']:
        if n=='range_total_scale':continue
        if n=='range_Bminus_shift':op,x,y='*','range_body_scale',2
        if n=='selection__q':op,x,y='*',32,'range_Bshift'
        source.append((n,op,x,y))
    source=sort_source(source,old['parameters']+old['auxiliaries'])
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==old['operations']-1
    assert counts['M']==old['multiplications']-1 and counts['A']==old['additions_subtractions']
    packet=dict(old,source=source,operations=len(source),multiplications=counts['M'],
        additions_subtractions=counts['A'],product_radix_scale=True,
        product_scale_parent=old,scale_exponent=a,scale_multiplier='32*B',
        native_scale_recipe='q=32*B*P^a; prescribed unpadded Q=q/16=2*B*P^a',
        removed_scale_register='range_total_scale',
        changed_scalar_ports=['range_Bminus_shift','selection__q'],
        equivalence_scope='Same accepted ordinary-input predicate for the fixed table, by direct typing and fresh positive native extensions; no same-native-tuple or arbitrary-output equality claim.')
    ss,out=polynomial_source(packet)
    assert ancestors(ss,[out])=={n for n,_,_,_ in ss}
    return packet


def build(codes=DEFAULT_CODES,alpha=24,beta=12,*,controller_mask=True,compute_length=True):
    return rewrite(parent.build(codes,alpha,beta,'joint',controller_mask,compute_length))


def degree_bound(packet):
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    value=lambda v:degrees[v] if isinstance(v,str) else 0
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    for n,op,a,b in packet['source']:
        degrees[n]=value(a)+value(b) if op=='*' else max(value(a),value(b))
        if n=='selection__R15':
            X,A,c,G='selection__wn2','selection__R12','selection__R10a','selection__gam'
            expected={n:('-', 'selection__L15','selection__Ac2'),
                'selection__L15':('*','selection__R14','selection__R14'),
                'selection__R14':('+','selection__D1',G),
                'selection__D1':('+',X,'selection__cam2'),
                'selection__cam2':('*',c,A),
                'selection__A':('+','selection__a_square','selection__a4m5'),
                'selection__a_square':('*',A,A),
                'selection__a4m5':('+','selection__a4',3),
                'selection__a4':('*',4,A),
                G:('*','selection__ga','selection__a4m5'),
                'selection__Ac2':('*','selection__A','selection__c2'),
                'selection__c2':('*',c,c)}
            assert all(rows[k]==v for k,v in expected.items())
            degrees[n]=max(2*value(X),value(X)+value(A)+value(c),value(X)+value(G),
                value(A)+value(c)+value(G),2*value(G),value('selection__a4m5')+2*value(c))
    outer=max(max(value(a),value(b)) for a,b in packet['comparisons'] if (a,b)!=('eight_units',1))
    unit=value('eight_units')
    assert unit==sum(value(f) for f in FACTORS)
    return dict(degree_upper_bound=unit+2*outer,unit_degree_bound=unit,
        factor_degree_bounds={f:value(f) for f in FACTORS},maximum_outer_residual_degree=outer,
        exact_degree_claimed=False)


def ledger(packet):
    source,out=polynomial_source(packet);counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    return dict(certificate=dict(operations=packet['operations'],multiplications=packet['multiplications'],
        additions_subtractions=packet['additions_subtractions'],equations=packet['equations'],witnesses=packet['positive_witnesses']),
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],output=out,**degree_bound(packet)))


def replay(source,values,overrides=None):
    env=dict(values);overrides={} if overrides is None else overrides
    for n,op,a,b in source:
        if n in overrides:env[n]=overrides[n];continue
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def source_audit(packet,cases=24,seed=244338):
    old=packet['product_scale_parent'];source,out=polynomial_source(packet);before_source,before_out=polynomial_source(old)
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in packet['parameters']+packet['auxiliaries']}
        a=execute(source,values);b=replay(before_source,values)
        T2=b['range_body_scale'];B=b['B']
        probe=replay(before_source,values,{'range_Bminus_shift':2*T2,'selection__q':32*B*T2})
        assert a[out]==probe[before_out]
        assert all(a[n]==probe[n] for n,_,_,_ in packet['source'])
        assert a['range_H']==b['range_H'] and a['range_Z']==b['range_Z']
        assert a['range_M']==b['range_M']+(3-B)*T2
        outer=[]
        for left,right in packet['comparisons']:
            if (left,right)==('eight_units',1):continue
            get=lambda env,v:env[v] if isinstance(v,str) else v
            r=get(a,left)-get(a,right);assert r==get(b,left)-get(b,right);outer.append(r)
        assert a[out]-b[before_out]==(a['eight_units']-b['eight_units'])*(1+sum(r*r for r in outer))
        counts['complete_changed_interface_register_residual_output_identities']+=1
        counts['signed_assignments']+=signed
    return dict(counts)


def scalar_bounds():
    rng=random.Random(244340);counts=Counter()
    # These are pretyping block fixtures, deliberately including nondyadic B,P.
    for _ in range(1024):
        B=rng.randrange(16,97);P=rng.randrange(max(B,12),151);a=rng.choice((18,24,40));T=P**a
        H0,M0,Z=[rng.randrange(T) for _ in range(3)]
        H=H0+B*T;M=M0+2*T;Q=2*B*T
        F=(16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8)
        assert min(F)>0 and sum(F)==16*Q-1 and max(F)<16*Q
        counts['positive_pretyping_block_margins']+=1
        counts['nondyadic_block_contexts']+=bool(B&(B-1) or P&(P-1))
    for b in range(4,10):
      for s in range(b,13):
        B=2**b;P=2**s;T=P**3
        for _ in range(16):
            H0,M0=rng.randrange(T),rng.randrange(T);Z=H0&M0
            assert (H0+B*T)&(M0+2*T)==Z
            counts['dyadic_top_block_AND_identities']+=1
    return dict(counts)


def path_checks():
    geometry=parent.geometry;model=geometry.parent.margin.parent.parent.parent
    physical=model.physical;counts=Counter()
    codes=tuple((i,) for i in range(1,9))
    for target in (24,36,48):
        u=target+1;word=model.reflect_codes((physical.target_word(target),))[0];states=model.trace(word,u)
        assert states[0]==[1,u,1,u] and states[-1]==[0,1,0,1]
        alpha,beta=1,u-2
        for controller_mask in (False,True):
          for comp in (False,True):
            packet=build(codes,alpha,beta,controller_mask=controller_mask,compute_length=comp)
            D=1<<max(u,1+max(abs(v) for row in states for v in row)).bit_length()
            B=16*D;P=B**len(word);J=(P-1)//(B-1)
            shifted=[[D-1+v for v in row] for row in states[:-1]]
            H=[sum(row[i]*B**j for j,row in enumerate(shifted)) for i in range(4)]
            Z=[sum((label==i+1)*shifted[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
            E=[sum((label==i)*B**j for j,label in enumerate(word)) for i in range(1,9)]
            values={n:1 for n in packet['parameters']+packet['auxiliaries']}
            values.update(x=1,height_slack=D-u,selection__bound_global=P-sum(H)-sum(Z)-7)
            if not comp:values['P']=P
            values.update({f'H{i}':v for i,v in enumerate(H)})
            values.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
            values.update({f'controller__edge_hat{i+1}':v+1 for i,v in enumerate(E)})
            assert min(values.values())>0
            env=execute(packet['source'],values)
            for left,right in packet['comparisons']:
                if (left,right)==('eight_units',1):continue
                assert (env[left] if isinstance(left,str) else left)==(env[right] if isinstance(right,str) else right)
            assert env['joint_bound_unit']==1 and env['computed_J']==J
            assert env['range_H']&env['range_M']==env['range_Z']
            assert env['selection__q']==32*B*P**packet['scale_exponent']
            counts['genuine_signed_shear_outer_histories']+=1;counts['chronological_rows']+=len(word)
    return dict(counts)


def guard_checks():
    old=parent.build(DEFAULT_CODES,variant='joint',controller_mask=True,compute_length=True);bad=[]
    for field,value in (('variant','strong'),('codes',((1,),)),('comparisons',old['comparisons'][:-1]),('source',old['source'][:-1])):
        changed=copy.deepcopy(old);changed[field]=value;bad.append(changed)
    rejected=0
    for packet in bad:
        try:rewrite(packet)
        except (AssertionError,KeyError,ValueError,TypeError):rejected+=1
        else:raise AssertionError('malformed parent accepted')
    try:build((),controller_mask=False)
    except AssertionError:rejected+=1
    else:raise AssertionError('empty table accepted outside contract')
    return dict(rejected_callers=rejected)


def verify():
    records=[]
    tables=(((1,),),((1,2),(3,4)),((8,6,4,2,7,5,3,1),),DEFAULT_CODES,((1,2,3,4,5,6,7,8)*2,))
    for codes in tables:
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            packet=build(codes,controller_mask=reuse,compute_length=comp)
            records.append(dict(codes=codes,controller_mask=reuse,compute_length=comp,
                ledger=ledger(packet),checks=source_audit(packet,seed=244000+len(records))))
    packet=build();source,out=polynomial_source(packet);default=ledger(packet)
    assert default['certificate']==dict(operations=227,multiplications=97,additions_subtractions=130,equations=6,witnesses=36)
    assert default['polynomial']['operations']==244 and default['polynomial']['multiplications']==103 and default['polynomial']['additions_subtractions']==141
    assert default['polynomial']['degree_upper_bound']==3396
    return dict(status='PASS_GROUP_PROJECTIVE_PRODUCT_RADIX_SCALE',default_ledger=default,
        source=source,output=out,source_sha256=hashlib.sha256(json.dumps(source).encode()).hexdigest(),
        ledgers=records,scalar_bounds=scalar_bounds(),paths=path_checks(),guards=guard_checks(),
        scope='Complete fixed-table ordinary-input equivalence with fresh native witnesses; the numerical universal subgroup alphabet is not instantiated, and244 is illustrative.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default_ledger'])
