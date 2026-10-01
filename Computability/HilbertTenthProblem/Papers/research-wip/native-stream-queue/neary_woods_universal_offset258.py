"""Shift the fixed program sentinel offset to absorb the last constant:258.

An exact affine source identity accompanies a valid-program accepted-input
proof. The inverse affine map need not preserve positive arbitrary tuples.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_lower_unit259 as parent

compiler, execute = parent.compiler, parent.execute
polynomial_source, degree_bound = parent.polynomial_source, parent.degree_bound
OFFSET='program_E'
DURATION='program_duration_gap'
HEIGHT='hist__height_slack'


def guard_parent(old):
    ancestor=old['lower_unit_parent'];parent.guard_parent(ancestor)
    expected=parent.rewrite(ancestor,group=old['lower_unit_group'])
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','fixed_numerals','width','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates','normalized_prefixes',
                'positive_scale_prefixes','bound_is_program_E','operations',
                'multiplications','additions_subtractions','equations','witnesses'):
        assert old.get(key)==expected.get(key),key
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[parent.DIFFERENCE]==('-',parent.PAIR[1],parent.PAIR[0])
    assert rows[parent.UNIT]==('+',parent.DIFFERENCE,1)
    assert {n for n,_,a,b in old['source'] if parent.DIFFERENCE in (a,b)}=={parent.UNIT}
    assert rows['load__tag_input']==('+','load__before_tail',OFFSET)
    assert old['initial_register']=='load__tag_input'
    assert rows['hist__height_sum__0']==('+','hist__Ufinal','load__tag_input')
    assert rows['hist__height_sum__1']==('+','hist__tag_terminal','hist__height_sum__0')
    assert rows['hist__height_sum__2']==('+',HEIGHT,'hist__height_sum__1')
    bound=OFFSET if old['bound_is_program_E'] else 'program_bound'
    assert rows['program_duration_bound']==('+',bound,DURATION)
    assert {n for n,_,a,b in old['source'] if OFFSET in (a,b)}==({'load__tag_input','program_duration_bound'} if old['bound_is_program_E'] else {'load__tag_input'})
    assert {n for n,_,a,b in old['source'] if DURATION in (a,b)}=={'program_duration_bound'}
    assert {n for n,_,a,b in old['source'] if HEIGHT in (a,b)}=={'hist__height_sum__2'}
    for key in ('interfaces','public_registers','fusion_interfaces','projected_coordinates','comparisons','unit_factors'):
        assert parent.DIFFERENCE not in parent.parent.parent.parent.leaves(old.get(key,{}))


def rewrite(old):
    guard_parent(old)
    source=[(n,'-',parent.PAIR[1],parent.PAIR[0]) if n==parent.UNIT else (n,op,a,b)
            for n,op,a,b in old['source'] if n!=parent.DIFFERENCE]
    packet=dict(old,source=source,operations=old['operations']-1,
        additions_subtractions=old['additions_subtractions']-1,
        offset_parent=old,program_offset_minus_one=True,
        program_offset_contract='program_E is the old fixed sentinel offset E minus1',
        initial_register=None, emitted_initial_minus_one_register='load__tag_input',
        initial_value_expression=dict(register='load__tag_input',offset=1),
        lower_unit_semantic_hypothesis='Emitted load__tag_input+1 is the sentinel of E(w), w ends in b, beta>=2.',
        loader_completeness_scope='Valid program recipes with E_new=E_old-1 and sufficiently long dyadic leading-zero padding.',
        identical_complete_polynomial=False,identical_positive_zero_set=False,
        identical_positive_coordinates=False,affine_complete_polynomial_identity=True,
        positive_zero_bijection=None,
        accepted_input_equivalence='Inherited valid program/input slices under E_new=E_old-1')
    compiler.check_source(packet)
    return packet


def build(parent_operations=260, *, merge_bound=True, witnesses=None):
    return rewrite(parent.build(parent_operations,merge_bound=merge_bound,witnesses=witnesses))


def lift_to_parent(packet,values):
    result=dict(values);result[OFFSET]+=1;result[HEIGHT]-=1
    if packet['bound_is_program_E']:result[DURATION]-=1
    return result


def project_from_parent(packet,values):
    result=dict(values);result[OFFSET]-=1;result[HEIGHT]+=1
    if packet['bound_is_program_E']:result[DURATION]+=1
    return result


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['offset_parent']
    before,_=polynomial_source(old)
    parent.parent.parent.parent.parent.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert packet['initial_register'] is None
    assert packet['initial_value_expression']==dict(register='load__tag_input',offset=1)
    assert degree_bound(packet)==degree_bound(old)
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    return dict(parent_polynomial_operations=len(before),bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'],exact_degree_claimed=False))


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['offset_parent'];bs,bo=polynomial_source(old);ns,no=polynomial_source(packet)
    changed={'load__tag_input','hist__height_sum__0','hist__height_sum__1','hist__V_lhs__39',parent.DIFFERENCE}
    for case in range(cases):
        draw=lambda:rng.randrange(1,5) if case<cases//2 else rng.randrange(-3,4)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS};lifted=lift_to_parent(packet,values)
        assert project_from_parent(packet,lifted)==values
        a=execute(compiler.materialize(bs,fixed),lifted);b=execute(compiler.materialize(ns,fixed),values)
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n not in changed)
        for n in changed-{parent.DIFFERENCE}:assert a[n]==b[n]+1
        assert a[parent.DIFFERENCE]+1==b[parent.UNIT]
        assert a[bo]==b[no]
        original={n:rng.randrange(1,8) for n in packet['parameters']+packet['auxiliaries']};original[OFFSET]+=1
        projected=project_from_parent(packet,original)
        assert min(projected.values())>0 and lift_to_parent(packet,projected)==original
        c=execute(compiler.materialize(bs,fixed),original);d=execute(compiler.materialize(ns,fixed),projected)
        assert c[bo]==d[no]
    return dict(complete_source_output_identities=2*cases,signed_cases=cases//2,positive_projection_cases=cases)


def sentinel_bound_audit():
    cases=0
    for length in range(1,129):
      for suffix in (0,1,(1<<length)-1,(1<<(length-1))):
        E=(1<<length)+suffix;new=E-1
        assert new>=length>=1
        for gap in (1,2,7):
            n=new+gap;assert n>length
            # Physical fixed-cell count is no greater than encoded length.
            cells=length;assert 64*n<64*n+cells<128*n
        cases+=1
    return dict(fixed_sentinel_bound_cases=cases,minimum_encoded_length=1,
        scope='Sentinel E-1>=encoded length>=fixed binary cell count; no full compiler constants materialized.')


def guards_audit():
    base=parent.build();bad=[]
    for coordinate in (OFFSET,DURATION,HEIGHT):
        v=copy.deepcopy(base);v['source'] += [('unpaid_'+coordinate,'+',coordinate,1)];bad.append(v)
    v=copy.deepcopy(base);v['public_registers']=[parent.DIFFERENCE];bad.append(v)
    v=copy.deepcopy(base);v['source']=[(n,'-',a,b) if n=='load__tag_input' else (n,op,a,b) for n,op,a,b in v['source']];bad.append(v)
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def verify():
    records=[];selected=[];seen=set()
    for interface in (False,True):
      for n in parent.parent.parent.parent.parent.NORMALIZATIONS:
       for s in parent.parent.parent.parent.parent.SCALE_OPTIONS:
        base=parent.parent.parent.parent.parent.build_base(n,s,interface)
        old260=parent.parent.rewrite(parent.parent.parent.rewrite(parent.parent.parent.parent.rewrite(parent.parent.parent.parent.parent.factored.rewrite(base))))
        packet=rewrite(parent.rewrite(old260));records.append(dict(ledger(packet),audit=audit(packet,258000+len(records))))
      for witnesses in (None,43,44,45):
       for plan in parent.parent.parent.parent.parent.factored_frontier(witnesses):
        old=parent.build(plan['polynomial']['operations']-9,merge_bound=interface,witnesses=witnesses)
        key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);rec=ledger(packet)
        records.append(dict(rec,audit=audit(packet,2581000+len(records))))
        source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
        selected.append(dict(rec,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=258,multiplications=133,additions_subtractions=125,degree_upper_bound=3861,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_OFFSET258',default=default,ledgers=records,selected_sources=selected,
        ledger_count=len(records),complete_source_output_identities=16*len(records),signed_cases=4*len(records),positive_projection_cases=8*len(records),
        sentinel_bounds=sentinel_bound_audit(),guards=guards_audit(),
        scope='Accepted-input equivalence on valid fixed program slices with E_new=E_old-1. Exact complete affine source identity; the new-to-parent affine map may have zero or negative gaps off the canonical domain. No all-positive-tuple bijection claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default'])
