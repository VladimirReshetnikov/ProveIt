"""Exact finite factor partitions after the U9 initial-bound recovery.

All sixteen inherited strong/scale bases, both bound interfaces and both
finalizers are covered. Only propagated bounds in this family are optimized.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_initial_bound254 as initial

preceding=initial.parent.parent.partitions
old=preceding.old
compiler=initial.compiler
EXPECTED=[(254,1379,43),(256,1237,43),(257,1191,43),(258,854,43),
          (259,601,44),(260,555,44),(261,454,44),(262,408,44),
          (263,302,44),(264,272,44),(265,228,44),(266,212,44)]


def apply_height_rewrites(packet):
    return initial.rewrite(initial.parent.rewrite(initial.parent.parent.rewrite(packet)))


@lru_cache(None)
def base(normalized,scaled,merge_bound=True):
    return apply_height_rewrites(preceding.base(normalized,scaled,merge_bound))


def regroup(original,partition,anchor):
    n=tuple(original['normalized_prefixes']);s=tuple(original.get('positive_scale_prefixes',()))
    interface=original['bound_is_program_E']
    assert original==base(n,s,interface),'requires a complete canonical initial254 base'
    assert len(original['group_products'])==1 and original['partition_anchor']==0
    # Rebuild each active parent with the same partition before applying its
    # guarded height map. Historical maps must not use a different finalizer.
    ancestor,_,_=preceding.regroup(preceding.base(n,s,interface),partition,anchor)
    packet=apply_height_rewrites(ancestor)
    source,output=initial.polynomial_source(packet)
    direct,direct_source,direct_output=old.regroup(original,partition,anchor)
    assert source==direct_source and output==direct_output
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','operations','multiplications','additions_subtractions','equations','witnesses'):
        assert packet.get(key)==direct.get(key),key
    packet=dict(packet,initial_bound_all_factor_partition=True,
        grouping_scope='Identical positive zeros within each initial254 base on valid shifted program/input slices; cross-base equivalence is existential')
    return packet,source,output


def record(original,partition,anchor):
    packet,source,output=regroup(original,partition,anchor)
    result=initial.ledger(packet)
    weights=[result['degree']['factor_degree_bounds'][n] for n in packet['unit_factors']]
    sums=[sum(weights[i] for i in group) for group in partition]
    residual=result['degree']['maximum_residual_degree_bound']
    # The field above includes new group comparisons, so obtain the retained
    # ordinary residual bound from the canonical single-group base instead.
    residual=initial.degree_bound(original)['maximum_residual_degree_bound']
    objective=2*max([residual]+sums) if anchor is None else sums[anchor]+2*max([residual]+[v for j,v in enumerate(sums) if j!=anchor])
    assert objective==result['polynomial']['degree_upper_bound']
    result.update(partition=[list(g) for g in partition],anchor=anchor,
        factor_names=packet['unit_factors'],factor_degree_bounds=weights,
        group_degree_bounds=sums,maximum_original_residual_degree_bound=residual,
        exact_objective_bound=objective)
    return result


@lru_cache(None)
def search(normalized,scaled):
    original=base(normalized,scaled);bounds=initial.degree_bound(original)
    weights=[bounds['factor_degree_bounds'][v] for v in original['unit_factors']]
    residual=bounds['maximum_residual_degree_bound']
    plans,statistics=old.solve(weights,residual)
    records=[record(original,p['partition'],p['anchor']) for p in plans]
    assert all(r['polynomial']['degree_upper_bound']==p['degree_upper_bound'] for r,p in zip(records,plans))
    maximum=max(weights);minimum=min(weights)
    floor=min(2*max(residual,maximum),maximum+2*residual,minimum+2*max(residual,maximum))
    assert floor>=212
    return dict(normalized_prefixes=normalized,positive_scale_prefixes=scaled,
        search_statistics=statistics,best_by_group_count=records,
        family_floor_certificate=dict(maximum_factor=maximum,minimum_factor=minimum,
            maximum_residual=residual,lower_bound=floor))


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None,43,44,45)
    rows=[r for n in old.NORMALIZATIONS for s in old.SCALE_OPTIONS
          if witnesses is None or 45-len(s)==witnesses
          for r in search(n,s)['best_by_group_count']]
    rows.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']))
    result=[];best=float('inf')
    for r in rows:
        if r['polynomial']['degree_upper_bound']<best:
            result.append(r);best=r['polynomial']['degree_upper_bound']
    return result


def build(operations=254,*,witnesses=None,merge_bound=True):
    plan=next(r for r in frontier(witnesses) if r['polynomial']['operations']==operations)
    original=base(tuple(plan['normalized_prefixes']),tuple(plan['positive_scale_prefixes']),merge_bound)
    return regroup(original,plan['partition'],plan['anchor'])[0]


def audit(original,partition,anchor,seed,cases=8):
    packet,source,output=regroup(original,partition,anchor)
    parent=packet['initial_bound_parent'];parent_source,parent_output=initial.polynomial_source(parent)
    core=old.partitions.factor_source(original);rng=random.Random(seed);nonpositive=0
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        numerals={n:draw() for n in compiler.NUMERALS}
        env=initial.execute(compiler.materialize(source,numerals),values)
        canonical=initial.execute(compiler.materialize(original['source'],numerals),values)
        assert all(env[n]==canonical[n] for n,_,_,_ in core)
        products=[]
        for group in partition:
            product=1
            for i in group:product*=canonical[original['unit_factors'][i]]
            products.append(product)
        assert products==[env[n] for n in packet['group_products']]
        val=lambda v:canonical[v] if isinstance(v,str) else v
        direct=sum((val(a)-val(b))**2 for a,b in original['comparisons'][:-1])
        direct+=sum((p-1)**2 for j,p in enumerate(products) if j!=anchor)
        if anchor is not None:direct=products[anchor]*(1+direct)-1
        assert env[output]==direct
        lifted=initial.lift_to_parent(packet,values,numerals)
        before=initial.execute(compiler.materialize(parent_source,numerals),lifted)
        assert before[parent_output]==env[output] and before[initial.HEIGHT]==values[initial.SLACK]
        assert all(before[n]==env[n] for n,_,_,_ in parent['source'] if n!=initial.HEIGHT)
        assert initial.project_from_parent(packet,lifted,numerals)==values
        nonpositive+=lifted[initial.SLACK]<=0
    return dict(direct_finalizer_and_group_checks=cases,complete_triangular_parent_identities=cases,
        signed_assignments=cases//2,nonpositive_algebraic_inverse_gaps=nonpositive)


def verify():
    studies=[search(n,s) for n in old.NORMALIZATIONS for s in old.SCALE_OPTIONS]
    summaries={str(w):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in frontier(w)] for w in (None,43,44,45)}
    assert summaries['None']==EXPECTED
    ledgers=[];selected=[];contexts=nonpositive=0
    for interface in (False,True):
      for study in studies:
        original=base(tuple(study['normalized_prefixes']),tuple(study['positive_scale_prefixes']),interface)
        for r in study['best_by_group_count']:
            ledgers.append(record(original,r['partition'],r['anchor']))
        count=len(original['unit_factors']);parts=[list(range(j,count,3)) for j in range(3)]
        for anchor in (None,0):
            check=audit(original,parts,anchor,2548540+contexts)
            contexts+=1;nonpositive+=check['nonpositive_algebraic_inverse_gaps']
      seen=set()
      for w in (None,43,44,45):
       for r in frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);original=base(key[0],key[1],interface)
        packet,source,output=regroup(original,r['partition'],r['anchor'])
        rec=record(original,r['partition'],r['anchor'])
        rec['audit']=audit(original,r['partition'],r['anchor'],2548550+contexts)
        contexts+=1;nonpositive+=rec['audit']['nonpositive_algebraic_inverse_gaps']
        encoded=compiler.encode_source(source)
        rec.update(source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest())
        selected.append(rec)
    mapped=json.loads(Path(initial.__file__).with_suffix('.json').read_text())['mapped_frontiers']
    improvements={}
    for key,rows in summaries.items():
        improvements[key]=[]
        for cost,degree,w in rows:
            previous=min((d for c,d,ww in mapped[key] if c<=cost),default=None)
            if previous is not None and degree<previous:
                improvements[key].append(dict(operations=cost,previous_mapped_bound=previous,new_bound=degree,witnesses=w))
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_INITIAL_BOUND_PARTITIONS',searches=studies,
        frontiers=summaries,mapped_family_improvements=improvements,ledgers=ledgers,selected_sources=selected,
        full_source_contexts=contexts,direct_finalizer_checks=8*contexts,
        complete_triangular_parent_identities=8*contexts,signed_assignments=4*contexts,
        nonpositive_algebraic_inverse_gaps=nonpositive,
        independent_search_validation=old.small_search_audit(),
        scope='Exact finite disjoint-partition/anchor objective for sixteen initial254 bases, optimizing guarded propagated-degree bounds. Both fixed program-bound interfaces checked. Within-base positive zeros agree on valid shifted-program slices; cross-base equivalence is existential. No exact-degree or global-circuit optimum.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print('Contexts',result['full_source_contexts'])
