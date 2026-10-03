"""Reuse a paid port polynomial in the native positive-scale bound.

The complete U9 polynomial still has254 operations. Its propagated default
degree falls to1203. The triangular source map is positive only at zeros.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_initial_bound_partitions as parent

initial=parent.initial
compiler,execute=initial.compiler,initial.execute
polynomial_source,degree_bound=initial.polynomial_source,initial.degree_bound
GAP='and__bound_beta'
BOUND='and__bs_X_bound'
INDEX='and__bs_packed'
PORT_BOUND='factored_pack_inner'


def leaves(value):
    return initial.leaves(value)


def cone(packet,roots):
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    seen=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in rows and n not in seen:
            seen.add(n);pending.extend(rows[n][1:])
    return [row for row in packet['source'] if row[0] in seen]


def guard(old):
    assert old.get('initial_bound_recovered') and not old.get('native_port_bound')
    assert 'and__' in old.get('positive_scale_prefixes',()),'joint positive scale is required'
    expected=initial.rewrite(old['initial_bound_parent'])
    # Regrouping adds only this provenance and its proved scope string.
    exempt={'initial_bound_all_factor_partition','grouping_scope'}
    assert {k:v for k,v in old.items() if k not in exempt}=={k:v for k,v in expected.items() if k not in exempt},'requires the complete guarded initial254 caller'
    assert old.get('grouping_scope') in (expected.get('grouping_scope'),
        'Identical positive zeros within each initial254 base on valid shifted program/input slices; cross-base equivalence is existential')
    if 'initial_bound_all_factor_partition' in old:assert old['initial_bound_all_factor_partition'] is True
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    required={
        BOUND:('+',INDEX,GAP),
        'and__wn2':('*',BOUND,'and__q'),
        'factored_pack_q_minus_one':('-','and__q',1),
        'factored_pack_q_plus_one':('+','and__q',1),
        'factored_pack_Z':('*','factored_pack_q_minus_one','and__F3'),
        'factored_pack_B':('+','and__padded_B','factored_pack_Z'),
        'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),
        PORT_BOUND:('+','factored_pack_A_plus_one','factored_pack_scaled_B'),
        INDEX:('*','factored_pack_q_minus_one',PORT_BOUND)}
    assert all(rows.get(n)==row for n,row in required.items())
    assert [n for n,_,a,b in old['source'] if GAP in (a,b)]==[BOUND]
    assert GAP in old['auxiliaries']
    for key in ('comparisons','unit_factors','interfaces','public_registers','fusion_interfaces','projected_coordinates'):
        assert GAP not in leaves(old.get(key)),key
    assert GAP not in leaves(cone(old,(INDEX,PORT_BOUND)))


def rewrite(old):
    guard(old)
    source=[(n,op,PORT_BOUND if n==BOUND else a,b) for n,op,a,b in old['source']]
    packet=dict(old,source=source,native_port_bound=True,native_port_bound_parent=old,
        native_port_bound_definition='and X=q*(S+beta), S=A+1+(q+1)*(Bport+(q-1)*Z), r=(q-1)*S, already paid',
        native_port_bound_map='beta_parent=beta_new+S-r; beta_new=beta_parent+r-S',
        positive_zero_bijection='On inherited valid shifted program/input slices; positivity of the reverse gap uses the recovered X=2^(2r+1)',
        identical_complete_polynomial=False,identical_positive_zero_set=False,
        triangular_complete_polynomial_identity=True,affine_complete_polynomial_identity=False)
    compiler.check_source(packet)
    assert len(source)==old['operations']
    return packet


def build(*,normalized=('geo__','and__'),scaled=('geo__','and__'),merge_bound=True,partition=None,anchor=0):
    original=parent.base(tuple(normalized),tuple(scaled),merge_bound)
    if partition is not None:original=parent.regroup(original,partition,anchor)[0]
    return rewrite(original)


def port_values(packet,values,numerals):
    env=execute(compiler.materialize(cone(packet,(INDEX,PORT_BOUND)),numerals),values)
    return env[INDEX],env[PORT_BOUND]


def lift_to_parent(packet,values,numerals):
    r,s=port_values(packet,values,numerals)
    result=dict(values);result[GAP]+=s-r;return result


def project_from_parent(packet,values,numerals):
    r,s=port_values(packet,values,numerals)
    result=dict(values);result[GAP]+=r-s;return result


def ledger(packet):
    old=packet['native_port_bound_parent']
    source,out=polynomial_source(packet);before,bo=polynomial_source(old)
    parent.old.inherited.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert [(n,op) for n,op,_,_ in source]==[(n,op) for n,op,_,_ in before]
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['comparisons']==old['comparisons']
    degree=degree_bound(packet);old_degree=degree_bound(old)
    assert degree['degree_upper_bound']<=old_degree['degree_upper_bound']
    return dict(bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet['positive_scale_prefixes'],
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree['degree_upper_bound'],exact_degree_claimed=False),
        degree=degree,parent_degree=old_degree)


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['native_port_bound_parent'];tally=Counter()
    ns,no=polynomial_source(packet);os,oo=polynomial_source(old)
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        v={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        if case==0:
            v={n:1 for n in v};fixed={n:2 for n in fixed}
        w=lift_to_parent(packet,v,fixed)
        assert project_from_parent(packet,w,fixed)==v
        a=execute(compiler.materialize(os,fixed),w);b=execute(compiler.materialize(ns,fixed),v)
        assert all(a[n]==b[n] for n,_,_,_ in old['source'])
        assert a[oo]==b[no]
        assert [a[n] for n in old['group_products']]==[b[n] for n in packet['group_products']]
        tally['complete_output_register_group_identities']+=1
        tally['signed_assignments']+=signed
        tally['nonpositive_formal_parent_gaps']+=w[GAP]<=0
        if case==0:assert w[GAP]<0;tally['positive_offzero_negative_parent_gaps']+=1
    return dict(tally)


def margins_audit():
    tally=Counter()
    for q in range(16,257,16):
      for z in range(8,q,16):
       for f1 in range(4,q-z,16):
        for f2 in range(2,q-z-f1,16):
            f0=q-1-z-f1-f2
            if f0<=0:continue
            a,b=z+f1,z+f2
            s=a+1+(q+1)*(b+(q-1)*z)
            r=f0+q*f1+q*q*f2+q**3*z
            assert r==(q-1)*s
            assert 0<a<q and 0<b<q and z>=8
            assert s>0 and q*s-r==s and r-s==(q-2)*s>0
            assert r>=q**3+q*q+q+1 and r<q**4
            for beta in (1,2,q):
                assert q*(s+beta)>r
                tally['pretyping_positive_bound_cases']+=1
            if q&(q-1):tally['nondyadic_scale_cases']+=1
            # A strict bit-length comparison proves the canonical inverse gap,
            # without materializing an exponentially large value of X.
            assert 2*r+1>=(q*r).bit_length()
            tally['canonical_exponential_margin_cases']+=1
    return dict(tally)


def guard_audit():
    old=parent.base(('geo__','and__'),('geo__','and__'));bad=[]
    for n in (BOUND,PORT_BOUND,INDEX):
        p=copy.deepcopy(old);p['source']=[(v,'-' if op=='+' else '+',a,b) if v==n else (v,op,a,b) for v,op,a,b in p['source']];bad.append(p)
    p=copy.deepcopy(old);p['source'].append(('bad_consumer','+',GAP,1));bad.append(p)
    for key in ('interfaces','public_registers'):
        p=copy.deepcopy(old);p[key]=dict(nested=[None,dict(hidden=GAP)]);bad.append(p)
    bad.append(parent.base(('geo__','and__'),('geo__',)))
    bad.append(rewrite(old))
    for packet in bad:
        try:rewrite(packet)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('invalid caller accepted')
    return len(bad)


def verify():
    records=[];sources=[];seen=set();totals=Counter()
    receipt=json.loads(Path(parent.__file__).with_suffix('.json').read_text())
    for interface in (False,True):
      plans=[]
      for n in parent.old.NORMALIZATIONS:
       for s in parent.old.SCALE_OPTIONS:
        if 'and__' not in s:continue
        base=parent.base(n,s,interface);count=len(base['unit_factors'])
        plans.append((base,None,0))
        groups=[list(range(j,count,3)) for j in range(3)]
        plans.extend((base,groups,anchor) for anchor in (None,0))
      for r in receipt['selected_sources']:
        s=tuple(r['positive_scale_prefixes'])
        if r['bound_is_program_E']!=interface or 'and__' not in s:continue
        base=parent.base(tuple(r['normalized_prefixes']),s,interface)
        plans.append((base,r['partition'],r['anchor']))
      for base,part,anchor in plans:
        old=base if part is None else parent.regroup(base,part,anchor)[0]
        key=(interface,tuple(old['normalized_prefixes']),tuple(old['positive_scale_prefixes']),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);record=ledger(packet)
        record['audit']=audit(packet,25412030+len(records));totals.update(record['audit']);records.append(record)
        if len(packet['group_products'])==1 and packet['partition_anchor']==0:
            source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
            sources.append(dict(record,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=254,multiplications=133,additions_subtractions=121,degree_upper_bound=1203,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_NATIVE_BOUND254',default=default,
        records=records,canonical_sources=sources,audit_totals=dict(totals),
        margins=margins_audit(),rejected_callers=guard_audit(),
        scope='Eight inherited bases with joint positive scale, both bound interfaces, selected and independent three-group schedules. Valid-slice positive-zero bijection; triangular all-integer source identity. No new partition optimization, exact-degree or global-circuit claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default']['polynomial']);print(result['audit_totals'])
