"""Remove a dominated terminal endpoint from the paid history height:256.

Exact affine complete-source identity; positive completeness and direct
soundness on valid program/input slices. No positive inverse is asserted.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_history_scale257 as parent
import neary_woods_universal_history_scale_partitions as partitions

compiler,execute=parent.compiler,parent.execute
polynomial_source,degree_bound=parent.polynomial_source,parent.degree_bound
REMOVED='hist__height_sum__0'
SUM='hist__height_sum__1'
HEIGHT='hist__height_sum__2'
SLACK='hist__height_slack'
UPPER='hist__Ufinal'
LOWER='hist__tag_terminal'
INITIAL='load__tag_input'


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):return set().union(set(),*(leaves(v) for v in value.values()))
    if isinstance(value,(list,tuple)):return set().union(set(),*(leaves(v) for v in value))
    return set()


def guard_parent(old):
    assert old.get('history_scale_from_bound') and not old.get('dominated_height_endpoint_removed')
    if old.get('history_scale_all_factor_partition'):
        base=partitions.base(tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),old['bound_is_program_E'])
        expected=partitions.regroup(base,old['factor_partition'],old['partition_anchor'])[0]
    else:
        expected=parent.rewrite(old['history_scale_parent'])
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','fixed_numerals','width','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates','normalized_prefixes',
                'positive_scale_prefixes','bound_is_program_E','operations',
                'multiplications','additions_subtractions','equations','witnesses',
                'initial_register','initial_value_expression','lower_unit_semantic_hypothesis'):
        assert old.get(key)==expected.get(key),key
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[REMOVED]==('+',UPPER,INITIAL)
    assert rows[SUM]==('+',LOWER,REMOVED)
    assert rows[HEIGHT]==('+',SLACK,SUM)
    assert rows['hist__tag_terminal_scale']==('*',compiler.Numeral('terminal_scale'),UPPER)
    assert rows[LOWER]==('+','hist__tag_terminal_scale',compiler.Numeral('terminal_offset'))
    assert {n for n,_,a,b in old['source'] if REMOVED in (a,b)}=={SUM}
    assert {n for n,_,a,b in old['source'] if SUM in (a,b)}=={HEIGHT}
    assert {n for n,_,a,b in old['source'] if SLACK in (a,b)}=={HEIGHT}
    for key in ('interfaces','public_registers','fusion_interfaces','projected_coordinates','comparisons','unit_factors'):
        assert not {REMOVED,SUM}&leaves(old.get(key,{}))


def rewrite(old):
    guard_parent(old)
    source=[(n,'+',LOWER,INITIAL) if n==SUM else (n,op,a,b)
            for n,op,a,b in old['source'] if n!=REMOVED]
    result=dict(old,source=source,operations=old['operations']-1,
        additions_subtractions=old['additions_subtractions']-1,
        height_parent=old,dominated_height_endpoint_removed=True,
        history_height_definition='D=emitted_initial_minus_one+tag_terminal+height_slack',
        height_endpoint_hypothesis='tag_terminal=terminal_scale*Ufinal+terminal_offset>Ufinal; both fixed numerals positive',
        historical_height_register=REMOVED,
        identical_complete_polynomial=False,affine_complete_polynomial_identity=True,
        identical_positive_zero_set=False,positive_zero_bijection=None,
        height_completeness_map='height_slack_new=height_slack_parent+Ufinal',
        accepted_input_equivalence='Inherited valid shifted program/input slices; direct soundness uses individual endpoint bounds')
    compiler.check_source(result)
    return result


def build(operations=256,*,merge_bound=True,witnesses=None):
    return rewrite(partitions.build(operations+1,merge_bound=merge_bound,witnesses=witnesses))


def lift_to_parent(packet,values):
    """Exact affine lift on all integer tuples, possibly nonpositive."""
    result=dict(values);result[SLACK]-=result[UPPER];return result


def project_from_parent(packet,values):
    result=dict(values);result[SLACK]+=result[UPPER];return result


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['height_parent'];before,_=polynomial_source(old)
    partitions.old.inherited.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert degree_bound(packet)==degree_bound(old)
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['comparisons']==old['comparisons']
    return dict(parent_polynomial_operations=len(before),bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'],exact_degree_claimed=False),
        degree=degree_bound(packet))


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['height_parent'];bs,bo=polynomial_source(old);ns,no=polynomial_source(packet)
    boundary=0
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        if case==0:values[SLACK]=values[UPPER]
        if case==1:values[SLACK]=1;values[UPPER]=2
        lifted=lift_to_parent(packet,values)
        assert project_from_parent(packet,lifted)==values
        a=execute(compiler.materialize(bs,fixed),lifted);b=execute(compiler.materialize(ns,fixed),values)
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n not in {REMOVED,SUM})
        assert a[SUM]==b[SUM]+values[UPPER] and a[bo]==b[no]
        assert a[REMOVED]==b[INITIAL]+values[UPPER]
        if case<2:assert lifted[SLACK]<=0;boundary+=1
        original={n:rng.randrange(1,8) for n in packet['parameters']+packet['auxiliaries']}
        projected=project_from_parent(packet,original)
        assert min(projected.values())>0 and lift_to_parent(packet,projected)==original
        c=execute(compiler.materialize(bs,fixed),original);d=execute(compiler.materialize(ns,fixed),projected)
        assert c[bo]==d[no]
    return dict(complete_output_and_retained_register_identities=2*cases,
        signed_assignments=cases//2,positive_parent_projections=cases,nonpositive_parent_height_boundaries=boundary)


def endpoint_audit():
    cases=0
    for upper in (1,2,3,17,257):
      for W in (1,2,7,31,1023):
       for scale in (1,2,8,32,256):
        for offset in (1,2,4,16):
         for eta in (1,2,upper):
          lower=scale*upper+offset;D=W+lower+eta
          assert D>=4 and 1<D and upper<lower<D and 0<=W-1<W+1<D
          assert upper+W+lower+(eta-upper)==D
          cases+=1
    return dict(pretyping_endpoint_cases=cases,
        scope='Positive endpoint/domain identities including nonpositive affine parent gaps; no native Pell zeros.')


def guards_audit():
    base=parent.build();bad=[]
    for coordinate in (REMOVED,SLACK):
        v=copy.deepcopy(base);v['source'].append(('extra_'+coordinate,'+',coordinate,1));bad.append(v)
    for key in ('public_registers','fusion_interfaces'):
        v=copy.deepcopy(base);v[key]=dict(nested=[None,REMOVED]);bad.append(v)
    for name in (SUM,'hist__tag_terminal_scale',LOWER):
        v=copy.deepcopy(base);v['source']=[(n,'-',a,b) if n==name else (n,op,a,b) for n,op,a,b in v['source']];bad.append(v)
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def verify():
    records=[];selected=[];seen=set()
    for interface in (False,True):
      for n in partitions.old.NORMALIZATIONS:
       for s in partitions.old.SCALE_OPTIONS:
        packet=rewrite(partitions.base(n,s,interface))
        records.append(dict(ledger(packet),audit=audit(packet,256000+len(records))))
      for w in (None,43,44,45):
       for plan in partitions.frontier(w):
        old=partitions.build(plan['polynomial']['operations'],merge_bound=interface,witnesses=w)
        key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);rec=ledger(packet)
        records.append(dict(rec,audit=audit(packet,2561000+len(records))))
        source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
        selected.append(dict(rec,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=256,multiplications=133,additions_subtractions=123,degree_upper_bound=1384,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_HEIGHT256',default=default,ledgers=records,selected_sources=selected,
        ledger_count=len(records),complete_output_and_retained_register_identities=16*len(records),
        signed_assignments=4*len(records),positive_parent_projections=8*len(records),
        nonpositive_parent_height_boundaries=2*len(records),endpoint_bounds=endpoint_audit(),guards=guards_audit(),
        mapped_frontiers={str(w):[(r['polynomial']['operations']-1,r['polynomial']['degree_upper_bound'],r['certificate']['witnesses'])
            for r in partitions.frontier(w)] for w in (None,43,44,45)},
        scope='Accepted-input equivalence on inherited valid shifted program slices, exact full affine source identity, positive completeness; no positive inverse claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default'])
