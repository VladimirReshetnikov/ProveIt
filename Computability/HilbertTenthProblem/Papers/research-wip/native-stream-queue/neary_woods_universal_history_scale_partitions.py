"""Every factor partition after the U9 history-scale reorientation.

The finite degree objective is exact; degrees remain conservative bounds.
Positive-zero equivalence is proved on valid shifted-program slices.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_history_unit_partitions as old
import neary_woods_universal_history_scale257 as scale
import neary_woods_universal_offset_partitions as offsets

compiler = old.compiler
EXPECTED = [(257,1384,43),(259,1242,43),(260,1196,43),(261,858,43),
            (262,606,44),(263,560,44),(264,458,44),(265,412,44),
            (266,306,44),(267,276,44),(268,230,44),(269,212,44)]


@lru_cache(None)
def base(normalized, scaled, merge_bound=True):
    return scale.rewrite(offsets.base(normalized,scaled,merge_bound))


def regroup(original, partition, anchor):
    assert original.get('history_scale_from_bound')
    packet,source,output = old.regroup(original,partition,anchor)
    parent,parent_source,_ = offsets.regroup(original['history_scale_parent'],partition,anchor)
    packet = dict(packet,history_scale_parent=parent,history_scale_all_factor_partition=True,
        grouping_scope='Identical positive zeros within the history-scale base on valid shifted-program slices.')
    assert len(source)==len(parent_source)-1
    return packet,source,output


def record(original, partition, anchor):
    packet,source,output = regroup(original,partition,anchor)
    result = old.record(original,partition,anchor)
    assert result['polynomial']['operations']==len(source)
    result.update(program_offset_minus_one=True,history_scale_from_bound=True,
        parent_polynomial_operations=len(source)+1)
    return result


@lru_cache(None)
def search(normalized, scaled):
    original=base(normalized,scaled)
    bounds=scale.degree_bound(original)
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


def build(operations=257, *, witnesses=None, merge_bound=True):
    plan=next(r for r in frontier(witnesses) if r['polynomial']['operations']==operations)
    original=base(tuple(plan['normalized_prefixes']),tuple(plan['positive_scale_prefixes']),merge_bound)
    return regroup(original,plan['partition'],plan['anchor'])[0]


def audit(original, partition, anchor, seed, cases=8):
    packet,source,output=regroup(original,partition,anchor)
    parent=packet['history_scale_parent'];ps,po=scale.polynomial_source(parent)
    rng=random.Random(seed);negative_slacks=0
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        values={v:draw() for v in packet['parameters']+packet['auxiliaries']}
        numerals={v:draw() for v in compiler.NUMERALS}
        material=compiler.materialize(source,numerals)
        parent_material=compiler.materialize(ps,numerals)
        env=scale.execute(material,values)
        val=lambda v:env[v] if isinstance(v,str) else v
        assert env[scale.SCALE]==sum(values[v] for v in
            ('hist__H_U','hist__H_V','hist__ZUhat0','hist__ZVhat0','hist__ZVhat1',scale.SLACK))
        assert env[scale.UNIT]==env[scale.SCALE]-env[scale.PRODUCT]
        products=[]
        for group in partition:
            product=1
            for i in group:product*=env[packet['unit_factors'][i]]
            products.append(product)
        assert products==[env[v] for v in packet['group_products']]
        direct=sum((val(a)-val(b))**2 for a,b in original['comparisons'][:-1])
        direct+=sum((v-1)**2 for j,v in enumerate(products) if j!=anchor)
        if anchor is not None:direct=products[anchor]*(direct+1)-1
        assert env[output]==direct
        # Force only the new repunit factor to +1. Other factors are arbitrary.
        constrained=dict(values)
        constrained[scale.SLACK]=env[scale.PRODUCT]+1-env[scale.SUM]
        old_values=dict(constrained);old_values[scale.SLACK]-=1
        new=scale.execute(material,constrained)
        before=scale.execute(parent_material,old_values)
        assert new[scale.UNIT]==before[scale.UNIT]==1
        assert all(new[v]==before[v] for v,_,_,_ in parent['source'] if v!=scale.BOUND)
        assert new[output]==before[po]
        negative_slacks+=old_values[scale.SLACK]<=0
    return dict(direct_finalizer_checks=cases,conditional_parent_output_identities=cases,
        signed_assignments=cases//2,nonpositive_algebraic_parent_slacks=negative_slacks)


def verify():
    studies=[search(n,s) for n in old.NORMALIZATIONS for s in old.SCALE_OPTIONS]
    summaries={str(w):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in frontier(w)] for w in (None,43,44,45)}
    assert summaries['None']==EXPECTED
    ledgers=[];selected=[];contexts=0;nonpositive=0
    for interface in (False,True):
      for study in studies:
        original=base(tuple(study['normalized_prefixes']),tuple(study['positive_scale_prefixes']),interface)
        for r in study['best_by_group_count']:
            ledgers.append(record(original,r['partition'],r['anchor']))
        count=len(original['unit_factors'])
        parts=[list(range(j,count,3)) for j in range(3)]
        for anchor in (None,0):
            check=audit(original,parts,anchor,2574000+contexts)
            contexts+=1;nonpositive+=check['nonpositive_algebraic_parent_slacks']
      seen=set()
      for w in (None,43,44,45):
       for r in frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);original=base(key[0],key[1],interface)
        packet,source,output=regroup(original,r['partition'],r['anchor'])
        rec=record(original,r['partition'],r['anchor'])
        rec['audit']=audit(original,r['partition'],r['anchor'],2575000+contexts)
        contexts+=1;nonpositive+=rec['audit']['nonpositive_algebraic_parent_slacks']
        encoded=compiler.encode_source(source)
        rec.update(source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest())
        selected.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_HISTORY_SCALE_PARTITIONS',searches=studies,
        frontiers=summaries,ledgers=ledgers,selected_sources=selected,
        full_source_contexts=contexts,direct_finalizer_checks=8*contexts,
        conditional_parent_output_identities=8*contexts,signed_assignments=4*contexts,
        nonpositive_algebraic_parent_slacks=nonpositive,
        independent_search_validation=old.small_search_audit(),
        scope='Exact finite disjoint-partition/anchor objective for sixteen history-scale native bases. '
              'Both program-bound interfaces checked; valid program recipes still use E_new=E_old-1. '
              'The parent polynomial agrees only on the +1 repunit locus under the one-unit slack map. '
              'Only conservative degree bounds are optimized; the separate75/87 frontier is unchanged.')



if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print('Contexts',result['full_source_contexts'])
