"""Exact finite regrouping after the U9 mask and history unit rewrites.

Both retained and absorbed lower transports, all sixteen inherited native
bases, and every disjoint factor partition are covered. Degree bounds only.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_lower_unit259 as lower

history = lower.parent
inherited = history.parent.parent.parent
partitions = inherited.partitions
compiler = lower.compiler
NORMALIZATIONS, SCALE_OPTIONS = inherited.NORMALIZATIONS, inherited.SCALE_OPTIONS
solve = inherited.scales.coupled_partitions.optimal_partitions
EXPECTED = [(259,3861,43),(261,3450,43),(262,3404,43),(263,2286,44),
            (264,1518,44),(265,1472,44),(266,1106,44),(267,1060,44),
            (268,738,44),(269,708,44),(270,608,44)]


@lru_cache(None)
def base(normalized, scaled, absorb_lower, merge_bound=True):
    assert normalized in NORMALIZATIONS and scaled in SCALE_OPTIONS
    assert type(absorb_lower) is bool and type(merge_bound) is bool
    raw = inherited.build_base(normalized, scaled, merge_bound)
    shared = history.parent.parent.rewrite(inherited.factored.rewrite(raw))
    current = history.rewrite(history.parent.rewrite(shared))
    result = lower.rewrite(current) if absorb_lower else current
    assert len(result['group_products']) == 1 and result['partition_anchor'] == 0
    return result


def regroup(original, partition, anchor):
    factors = original['unit_factors']
    assert all(partition) and sorted(i for g in partition for i in g) == list(range(len(factors)))
    assert anchor is None or type(anchor) is int and 0 <= anchor < len(partition)
    core = partitions.factor_source(original)
    source, products = list(core), []
    for j, group in enumerate(partition):
        last = factors[group[0]]
        for k, i in enumerate(group[1:]):
            nxt = f'history_partition_product_{j}_{k}'
            source.append((nxt, '*', last, factors[i])); last = nxt
        products.append(last)
    ordinary = original['comparisons'][:-1]
    pairs = ordinary + [(p,1) for j,p in enumerate(products) if j != anchor]
    if anchor is not None: pairs.append((products[anchor],1))
    counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in source)
    packet = dict(original, source=source, comparisons=pairs,
        operations=len(source), multiplications=counts['M'], additions_subtractions=counts['A'],
        equations=len(pairs), factor_partition=[list(g) for g in partition],
        partition_anchor=anchor, group_products=products,
        unit_register=None if anchor is None else products[anchor], unit_product=anchor is not None,
        history_all_factor_partition=True,
        grouping_scope='Identical complete positive zeros within one fixed base on valid program/input slices.')
    compiler.check_source(packet)
    literal, output = lower.polynomial_source(packet)
    inherited.loader.source_closure(literal, output)
    cost = len(core)+len(factors)+3*len(ordinary)-1+2*len(partition)
    zero_residual_anchor = not ordinary and len(partition)==1 and anchor==0
    assert len(literal) == cost-int(zero_residual_anchor)
    return packet, literal, output


def record(original, partition, anchor):
    packet, literal, output = regroup(original, partition, anchor)
    bound = lower.degree_bound(original)
    weights = [bound['factor_degree_bounds'][n] for n in original['unit_factors']]
    sums = [sum(weights[i] for i in group) for group in partition]
    residual = bound['maximum_residual_degree_bound']
    degree = (2*max([residual]+sums) if anchor is None else
              sums[anchor]+2*max([residual]+[v for j,v in enumerate(sums) if j != anchor]))
    actual = lower.degree_bound(packet)
    assert actual['degree_upper_bound'] == degree
    pc = Counter('M' if op == '*' else 'A' for _,op,_,_ in literal)
    return dict(normalized_prefixes=original['normalized_prefixes'],
        positive_scale_prefixes=original.get('positive_scale_prefixes',()),
        absorbed_lower_transport=lower.UNIT in original['unit_factors'],
        bound_is_program_E=original['bound_is_program_E'],
        partition=partition, anchor=anchor, factor_names=original['unit_factors'],
        factor_degree_bounds=weights, group_degree_bounds=sums,
        maximum_original_residual_degree_bound=residual,
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(literal),multiplications=pc['M'],additions_subtractions=pc['A'],
            degree_upper_bound=degree, exact_degree_claimed=False, output=output))


@lru_cache(None)
def search(normalized, scaled, absorb_lower):
    original = base(normalized, scaled, absorb_lower)
    bound = lower.degree_bound(original)
    weights = [bound['factor_degree_bounds'][n] for n in original['unit_factors']]
    plans, statistics = solve(weights,bound['maximum_residual_degree_bound'])
    records = [record(original,p['partition'],p['anchor']) for p in plans]
    assert all(r['polynomial']['degree_upper_bound']==p['degree_upper_bound'] for r,p in zip(records,plans))
    return dict(normalized_prefixes=normalized, positive_scale_prefixes=scaled,
        absorbed_lower_transport=absorb_lower, search_statistics=statistics, best_by_group_count=records)


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None,43,44,45)
    choices = [r for n in NORMALIZATIONS for s in SCALE_OPTIONS
        if witnesses is None or 45-len(s)==witnesses
        for absorbed in (False,True) for r in search(n,s,absorbed)['best_by_group_count']]
    choices.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],
        r['certificate']['witnesses'],r['absorbed_lower_transport']))
    result, least = [], float('inf')
    for r in choices:
        if r['polynomial']['degree_upper_bound'] < least:
            result.append(r); least=r['polynomial']['degree_upper_bound']
    return result


def build(operations=259, *, witnesses=None, merge_bound=True):
    chosen = next(r for r in frontier(witnesses) if r['polynomial']['operations']==operations)
    original = base(tuple(chosen['normalized_prefixes']),tuple(chosen['positive_scale_prefixes']),
                    chosen['absorbed_lower_transport'],merge_bound)
    return regroup(original,chosen['partition'],chosen['anchor'])[0]


def audit(original, partition, anchor, seed, cases=8):
    packet, source, output = regroup(original,partition,anchor)
    core = partitions.factor_source(original)
    rng = random.Random(seed)
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        numerals={n:draw() for n in compiler.NUMERALS}
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        before=lower.execute(compiler.materialize(original['source'],numerals),values)
        after=lower.execute(compiler.materialize(source,numerals),values)
        assert all(after[n]==before[n] for n,_,_,_ in core)
        val=lambda n:before[n] if isinstance(n,str) else n
        residuals=sum((val(a)-val(b))**2 for a,b in original['comparisons'][:-1])
        products=[]
        for group in partition:
            p=1
            for i in group:p*=before[original['unit_factors'][i]]
            products.append(p)
        expected=residuals+sum((p-1)**2 for j,p in enumerate(products) if j!=anchor)
        if anchor is not None:expected=products[anchor]*(expected+1)-1
        assert after[output]==expected
    return dict(complete_output_and_retained_register_checks=cases,signed_cases=cases//2)


def small_search_audit():
    # Independent Bell enumeration, including zero ordinary residuals and
    # the one-operation special case. The subset optimizer supplies no oracle.
    rng=random.Random(2591106); instances=enumerated=0
    for n in range(1,8):
      for residual in (0,7,19):
        weights=[rng.randrange(1,32) for _ in range(n)]
        best={}
        for partition in partitions.set_partitions(list(range(n))):
            sums=[sum(weights[i] for i in g) for g in partition]
            for anchor in [None]+list(range(len(partition))):
                degree=2*max([residual]+sums) if anchor is None else sums[anchor]+2*max([residual]+[v for j,v in enumerate(sums) if j!=anchor])
                key=len(partition)
                best[key]=min(best.get(key,degree),degree)
                enumerated+=1
        answer,_=solve(weights,residual)
        assert best=={p['groups']:p['degree_upper_bound'] for p in answer}
        instances+=1
    return dict(independent_weighted_instances=instances,enumerated_partition_anchor_choices=enumerated)


def verify():
    studies=[search(n,s,a) for n in NORMALIZATIONS for s in SCALE_OPTIONS for a in (False,True)]
    summaries={str(w):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in frontier(w)] for w in (None,43,44,45)}
    assert summaries['None']==EXPECTED
    ledgers=[];examples=[];contexts=0
    for interface in (False,True):
      for study in studies:
        original=base(tuple(study['normalized_prefixes']),tuple(study['positive_scale_prefixes']),study['absorbed_lower_transport'],interface)
        for r in study['best_by_group_count']:
            ledgers.append(record(original,r['partition'],r['anchor']))
        # Exercise both finalizers, independent of which one the degree planner selects.
        n=len(original['unit_factors']);parts=[list(range(j,n,3)) for j in range(3)]
        for anchor in (None,0):
            audit(original,parts,anchor,2592000+contexts);contexts+=1
      seen=set()
      for w in (None,43,44,45):
       for r in frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),r['absorbed_lower_transport'],tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key)
        original=base(key[0],key[1],key[2],interface)
        packet,source,output=regroup(original,r['partition'],r['anchor'])
        rec=record(original,r['partition'],r['anchor'])
        rec['audit']=audit(original,r['partition'],r['anchor'],2593000+contexts);contexts+=1
        encoded=compiler.encode_source(source)
        rec.update(source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest())
        examples.append(rec)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_HISTORY_UNIT_PARTITIONS',searches=studies,
        frontiers=summaries,ledgers=ledgers,selected_sources=examples,
        full_source_contexts=contexts,complete_output_checks=8*contexts,signed_cases=4*contexts,
        independent_search_validation=small_search_audit(),
        scope='Exact all-factor disjoint-partition optimization under the stated propagated-degree objective, '
              'over sixteen inherited native bases and optional lower history unit. Both fixed program-bound '
              'interfaces are audited. Valid program/input slices are retained. No exact degree or global '
              'arithmetic minimum claimed; the separate75/87 bounds remain unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print('Contexts',result['full_source_contexts'])
