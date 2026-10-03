"""Every factor partition for the shifted-offset U9 universal compiler.

The finite degree objective is exact; degrees remain conservative bounds.
The affine old-offset identity commutes with each chosen finalizer.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_history_unit_partitions as old
import neary_woods_universal_offset258 as shift

compiler = old.compiler
EXPECTED = [(258,3861,43),(260,3455,43),(261,3409,43),(262,2291,44),
            (263,1523,44),(264,1477,44),(265,1112,44),(266,1066,44),
            (267,742,44),(268,712,44),(269,608,44)]


@lru_cache(None)
def base(normalized, scaled, merge_bound=True):
    return shift.rewrite(old.base(normalized,scaled,True,merge_bound))


def regroup(original, partition, anchor):
    assert original.get('program_offset_minus_one')
    packet,source,output = old.regroup(original,partition,anchor)
    parent,parent_source,_ = old.regroup(original['offset_parent'],partition,anchor)
    # The active affine parent must have the SAME partition and finalizer.
    packet = dict(packet,offset_parent=parent,offset_all_factor_partition=True,
        grouping_scope='Identical positive zeros within the shifted-offset base on valid program/input slices.')
    assert len(source)==len(parent_source)-1
    assert shift.degree_bound(packet)==shift.degree_bound(parent)
    return packet,source,output


def record(original, partition, anchor):
    packet,source,output = regroup(original,partition,anchor)
    result = old.record(original,partition,anchor)
    assert result['polynomial']['operations']==len(source)
    result.update(program_offset_minus_one=True,
        parent_polynomial_operations=len(source)+1)
    return result


@lru_cache(None)
def search(normalized, scaled):
    original=base(normalized,scaled)
    bounds=shift.degree_bound(original)
    weights=[bounds['factor_degree_bounds'][v] for v in original['unit_factors']]
    plans,statistics=old.solve(weights,bounds['maximum_residual_degree_bound'])
    records=[record(original,p['partition'],p['anchor']) for p in plans]
    assert all(r['polynomial']['degree_upper_bound']==p['degree_upper_bound'] for r,p in zip(records,plans))
    return dict(normalized_prefixes=normalized,positive_scale_prefixes=scaled,
        search_statistics=statistics,best_by_group_count=records)


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None,43,44,45)
    rows=[r for n in old.NORMALIZATIONS for s in old.SCALE_OPTIONS
          if witnesses is None or 45-len(s)==witnesses
          for r in search(n,s)['best_by_group_count']]
    rows.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']))
    result=[];least=float('inf')
    for r in rows:
        if r['polynomial']['degree_upper_bound']<least:
            result.append(r);least=r['polynomial']['degree_upper_bound']
    return result


def build(operations=258, *, witnesses=None, merge_bound=True):
    plan=next(r for r in frontier(witnesses) if r['polynomial']['operations']==operations)
    original=base(tuple(plan['normalized_prefixes']),tuple(plan['positive_scale_prefixes']),merge_bound)
    return regroup(original,plan['partition'],plan['anchor'])[0]


def audit(original, partition, anchor, seed, cases=8):
    packet,source,output=regroup(original,partition,anchor)
    parent=packet['offset_parent'];ps,po=shift.polynomial_source(parent)
    rng=random.Random(seed);zero_gaps=0
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        values={v:draw() for v in packet['parameters']+packet['auxiliaries']}
        if case==0:
            values[shift.HEIGHT]=1;values[shift.DURATION]=1
        numerals={v:draw() for v in compiler.NUMERALS}
        parent_values=shift.lift_to_parent(packet,values)
        assert shift.project_from_parent(packet,parent_values)==values
        zero_gaps+=parent_values[shift.HEIGHT]==0
        a=shift.execute(compiler.materialize(ps,numerals),parent_values)
        b=shift.execute(compiler.materialize(source,numerals),values)
        assert a[po]==b[output]
        assert all(a[v]==b[v] for v in packet['unit_factors'])
        val=lambda v:b[v] if isinstance(v,str) else v
        products=[]
        for group in partition:
            product=1
            for i in group:product*=b[packet['unit_factors'][i]]
            products.append(product)
        ordinary=sum((val(a)-val(c))**2 for a,c in original['comparisons'][:-1])
        direct=ordinary+sum((v-1)**2 for j,v in enumerate(products) if j!=anchor)
        if anchor is not None:direct=products[anchor]*(direct+1)-1
        assert b[output]==direct
        positive={v:rng.randrange(1,8) for v in packet['parameters']+packet['auxiliaries']}
        positive[shift.OFFSET]+=1
        projected=shift.project_from_parent(packet,positive)
        assert min(projected.values())>0 and shift.lift_to_parent(packet,projected)==positive
        a=shift.execute(compiler.materialize(ps,numerals),positive)
        b=shift.execute(compiler.materialize(source,numerals),projected)
        assert a[po]==b[output]
    return dict(affine_output_identities=2*cases,signed_affine_cases=cases//2,
        direct_finalizer_checks=cases,positive_projection_cases=cases,
        zero_parent_height_cases=zero_gaps)


def verify():
    studies=[search(n,s) for n in old.NORMALIZATIONS for s in old.SCALE_OPTIONS]
    summaries={str(w):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in frontier(w)] for w in (None,43,44,45)}
    assert summaries['None']==EXPECTED
    ledgers=[];selected=[];contexts=0;zero_gaps=0
    for interface in (False,True):
      for study in studies:
        original=base(tuple(study['normalized_prefixes']),tuple(study['positive_scale_prefixes']),interface)
        for r in study['best_by_group_count']:
            ledgers.append(record(original,r['partition'],r['anchor']))
        count=len(original['unit_factors'])
        parts=[list(range(j,count,3)) for j in range(3)]
        for anchor in (None,0):
            check=audit(original,parts,anchor,2584000+contexts)
            contexts+=1;zero_gaps+=check['zero_parent_height_cases']
      seen=set()
      for w in (None,43,44,45):
       for r in frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);original=base(key[0],key[1],interface)
        packet,source,output=regroup(original,r['partition'],r['anchor'])
        rec=record(original,r['partition'],r['anchor'])
        rec['audit']=audit(original,r['partition'],r['anchor'],2585000+contexts)
        contexts+=1;zero_gaps+=rec['audit']['zero_parent_height_cases']
        encoded=compiler.encode_source(source)
        rec.update(source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest())
        selected.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_OFFSET_PARTITIONS',searches=studies,
        frontiers=summaries,ledgers=ledgers,selected_sources=selected,
        full_source_contexts=contexts,affine_output_identities=16*contexts,
        signed_affine_cases=4*contexts,direct_finalizer_checks=8*contexts,
        positive_projection_cases=8*contexts,zero_parent_height_cases=zero_gaps,
        independent_search_validation=old.small_search_audit(),
        scope='Exact finite disjoint-partition/anchor objective for all sixteen shifted-offset native bases. '
              'Both program-bound interfaces checked; valid program recipes use E_new=E_old-1. '
              'The affine identity commutes with every finalizer but is not an all-positive-tuple bijection. '
              'Only conservative degree bounds are optimized; the separate75/87 frontier is unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print('Contexts',result['full_source_contexts'])
