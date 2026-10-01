"""Exact finite partitions after the product history scale.

Eight joint-scale bases use b*P^9 and reserved tags2,1; the other eight
retain their native-bound partition bases. Only propagated bounds optimized.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_native_bound_partitions as previous
import neary_woods_universal_product_scale253 as product

bound=previous.bound
initial=previous.initial
engine=previous.engine
compiler=product.compiler
polynomial_source,degree_bound=product.polynomial_source,product.degree_bound
EXPECTED=[(253,1147,43),(255,1013,43),(256,967,43),(257,710,43),
          (258,664,43),(259,488,43),(261,372,43),(263,302,44),
          (264,272,44),(265,228,44),(266,212,44)]


def apply_product(packet):
    return product.rewrite(packet) if 'and__' in packet.get('positive_scale_prefixes',()) else packet


@lru_cache(None)
def base(normalized,scaled,merge_bound=True):
    return apply_product(previous.base(normalized,scaled,merge_bound))


def regroup(original,partition,anchor):
    n=tuple(original['normalized_prefixes']);s=tuple(original.get('positive_scale_prefixes',()))
    interface=original['bound_is_program_E']
    assert original==base(n,s,interface),'requires a complete canonical mixed product-scale base'
    assert len(original['group_products'])==1 and original['partition_anchor']==0
    parent_packet,_,_=previous.regroup(previous.base(n,s,interface),partition,anchor)
    if 'and__' in s:
        # Reconstruct the exact guarded254 caller. The prior optimizer adds only
        # two scope/provenance fields, never additional arithmetic or exports.
        old=bound.rewrite(parent_packet['native_port_bound_parent'])
        assert parent_packet==dict(old,native_bound_all_factor_partition=True,
            native_bound_partition_scope='Identical positive zeros within one of the sixteen mixed bases on valid shifted program/input slices; cross-base equivalence is existential')
        packet=product.rewrite(old)
    else:
        packet=parent_packet
    source,output=polynomial_source(packet)
    direct,direct_source,direct_output=engine.regroup(original,partition,anchor)
    assert source==direct_source and output==direct_output
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','operations','multiplications','additions_subtractions','equations','witnesses'):
        assert packet.get(key)==direct.get(key),key
    return dict(packet,product_scale_all_factor_partition=True,
        product_scale_partition_scope='Identical positive zeros within one of the sixteen mixed bases on valid shifted program/input slices; cross-base and preceding-scale equivalence is existential'),source,output


def record(original,partition,anchor):
    packet,source,output=regroup(original,partition,anchor)
    engine.inherited.loader.source_closure(source,output)
    actual=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    cert=Counter('M' if op=='*' else 'A' for _,op,_,_ in packet['source'])
    assert (len(packet['source']),cert['M'],cert['A'])==(packet['operations'],packet['multiplications'],packet['additions_subtractions'])
    assert packet['parameters']==original['parameters'] and packet['auxiliaries']==original['auxiliaries']
    degrees=degree_bound(packet);canonical_degrees=degree_bound(original)
    weights=[degrees['factor_degree_bounds'][v] for v in packet['unit_factors']]
    assert weights==[canonical_degrees['factor_degree_bounds'][v] for v in original['unit_factors']]
    sums=[sum(weights[i] for i in group) for group in partition]
    residual=canonical_degrees['maximum_residual_degree_bound']
    objective=2*max([residual]+sums) if anchor is None else sums[anchor]+2*max([residual]+[v for j,v in enumerate(sums) if j!=anchor])
    assert objective==degrees['degree_upper_bound']
    core=len(engine.partitions.factor_source(original));nf=len(weights);m=len(original['comparisons'])-1;g=len(partition)
    cost=core+nf if m==0 and g==1 and anchor is not None else core+nf+3*m-1+2*g
    assert cost==len(source)
    return dict(bound_is_program_E=packet['bound_is_program_E'],
        native_port_bound=bool(packet.get('native_port_bound')),
        product_history_scale=bool(packet.get('product_history_scale')),
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=actual['M'],additions_subtractions=actual['A'],
            degree_upper_bound=degrees['degree_upper_bound'],exact_degree_claimed=False),
        degree=degrees,partition=[list(g) for g in partition],anchor=anchor,
        factor_names=packet['unit_factors'],factor_degree_bounds=weights,group_degree_bounds=sums,
        maximum_original_residual_degree_bound=residual,exact_objective_bound=objective,
        core_operations=core,ordinary_comparisons=m)


@lru_cache(None)
def search(normalized,scaled):
    original=base(normalized,scaled);degrees=degree_bound(original)
    weights=[degrees['factor_degree_bounds'][v] for v in original['unit_factors']]
    residual=degrees['maximum_residual_degree_bound']
    plans,statistics=engine.solve(weights,residual)
    records=[record(original,p['partition'],p['anchor']) for p in plans]
    assert all(r['polynomial']['degree_upper_bound']==p['degree_upper_bound'] for r,p in zip(records,plans))
    maximum=max(weights);minimum=min(weights)
    floor=min(2*max(residual,maximum),maximum+2*residual,minimum+2*max(residual,maximum))
    assert floor>=212
    if len(scaled)==2:assert floor>=372
    return dict(normalized_prefixes=normalized,positive_scale_prefixes=scaled,
        native_port_bound=bool(original.get('native_port_bound')),
        product_history_scale=bool(original.get('product_history_scale')),
        search_statistics=statistics,best_by_group_count=records,
        family_floor_certificate=dict(maximum_factor=maximum,minimum_factor=minimum,
            maximum_residual=residual,lower_bound=floor))


@lru_cache(None)
def frontier(witnesses=None):
    assert witnesses in (None,43,44,45)
    rows=[r for n in engine.NORMALIZATIONS for s in engine.SCALE_OPTIONS
          if witnesses is None or 45-len(s)==witnesses
          for r in search(n,s)['best_by_group_count']]
    rows.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']))
    result=[];best=float('inf')
    for r in rows:
        if r['polynomial']['degree_upper_bound']<best:
            result.append(r);best=r['polynomial']['degree_upper_bound']
    return result


def build(operations=253,*,witnesses=None,merge_bound=True):
    plan=next(r for r in frontier(witnesses) if r['polynomial']['operations']==operations)
    original=base(tuple(plan['normalized_prefixes']),tuple(plan['positive_scale_prefixes']),merge_bound)
    return regroup(original,plan['partition'],plan['anchor'])[0]


def execute_with_ports(source,values,overrides):
    env=dict(values)
    for name,op,left,right in source:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=overrides[name] if name in overrides else a*b if op=='*' else a+b if op=='+' else a-b
    return env


def audit(original,partition,anchor,seed,cases=8):
    packet,source,output=regroup(original,partition,anchor)
    before_product=packet['product_history_scale_parent'] if packet.get('product_history_scale') else packet
    before_bound=before_product['native_port_bound_parent'] if packet.get('native_port_bound') else before_product
    parent255=before_bound['initial_bound_parent'];ps,po=polynomial_source(parent255)
    core=engine.partitions.factor_source(original);rng=random.Random(seed);totals=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        numerals={n:draw() for n in compiler.NUMERALS}
        env=bound.execute(compiler.materialize(source,numerals),values)
        canonical=bound.execute(compiler.materialize(original['source'],numerals),values)
        assert all(env[n]==canonical[n] for n,_,_,_ in core)
        products=[]
        for group in partition:
            value=1
            for i in group:value*=canonical[original['unit_factors'][i]]
            products.append(value)
        assert products==[env[n] for n in packet['group_products']]
        val=lambda v:canonical[v] if isinstance(v,str) else v
        direct=sum((val(a)-val(b))**2 for a,b in original['comparisons'][:-1])
        direct+=sum((p-1)**2 for j,p in enumerate(products) if j!=anchor)
        if anchor is not None:direct=products[anchor]*(1+direct)-1
        assert env[output]==direct
        lifted=dict(values);overrides={}
        if packet.get('product_history_scale'):
            P=env[product.P];b=env[product.B];q0=env[product.LOW]
            overrides={product.TOP_TWO:2*P**9,product.H:env[product.HLOW]+2*P**9,
                       product.M:env[product.MLOW]+P**9,'and__q':q0*b*P**9}
        if packet.get('native_port_bound'):
            lifted[bound.GAP]+=env[bound.PORT_BOUND]-env[bound.INDEX]
            totals['native_gap_lifts']+=1
            totals['nonpositive_native_parent_gaps']+=lifted[bound.GAP]<=0
        lifted[initial.SLACK]-=env[initial.INITIAL]
        before=execute_with_ports(compiler.materialize(ps,numerals),lifted,overrides)
        assert before[initial.HEIGHT]==values[initial.SLACK]
        assert before[po]==env[output]
        for name,_,_,_ in packet['source']:
            if name in before and name!=initial.HEIGHT:assert before[name]==env[name],name
        roundtrip=dict(lifted);roundtrip[initial.SLACK]+=before[initial.INITIAL]
        if packet.get('native_port_bound'):
            roundtrip[bound.GAP]+=before[bound.INDEX]-before[bound.PORT_BOUND]
        assert roundtrip==values
        totals['direct_scalar_group_finalizer_checks']+=1
        totals['complete_composed_register_output_replays']+=1
        totals['changed_port_replays' if overrides else 'unchanged_port_parent_identities']+=1
        totals['signed_assignments']+=signed
        totals['nonpositive_height_parent_gaps']+=lifted[initial.SLACK]<=0
    return dict(totals)


def guard_audit():
    original=base(('geo__','and__'),('geo__','and__'));bad=[]
    bad.append(dict(original,parameters=['wrong']+original['parameters'][1:]))
    bad.append(dict(original,source=original['source']+[('private_extra','+',bound.GAP,1)]))
    bad.append(dict(original,public_registers=dict(hidden=[bound.GAP])))
    bad.append(dict(original,source=[(n,'-',a,b) if n==bound.BOUND else (n,op,a,b) for n,op,a,b in original['source']]))
    for p in bad:
        try:regroup(p,[list(range(len(p['unit_factors'])))],0)
        except AssertionError:pass
        else:raise AssertionError('incompatible base accepted')
    return len(bad)


def verify():
    studies=[search(n,s) for n in engine.NORMALIZATIONS for s in engine.SCALE_OPTIONS]
    summaries={str(w):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in frontier(w)] for w in (None,43,44,45)}
    assert summaries['None']==EXPECTED
    assert min(r['family_floor_certificate']['lower_bound'] for r in studies)==212
    assert min(r['family_floor_certificate']['lower_bound'] for r in studies if len(r['positive_scale_prefixes'])==2)==372
    ledgers=[];selected=[];contexts=0;totals=Counter()
    for interface in (False,True):
      for study in studies:
        original=base(tuple(study['normalized_prefixes']),tuple(study['positive_scale_prefixes']),interface)
        for r in study['best_by_group_count']:
            ledgers.append(record(original,r['partition'],r['anchor']))
        count=len(original['unit_factors']);parts=[list(range(j,count,4)) for j in range(4)]
        for anchor in (None,0):
            totals.update(audit(original,parts,anchor,25371000+contexts));contexts+=1
      seen=set()
      for w in (None,43,44,45):
       for r in frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);original=base(key[0],key[1],interface)
        packet,source,output=regroup(original,r['partition'],r['anchor'])
        rec=record(original,r['partition'],r['anchor'])
        rec['audit']=audit(original,r['partition'],r['anchor'],25371100+contexts)
        totals.update(rec['audit']);contexts+=1
        encoded=compiler.encode_source(source)
        rec.update(source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest())
        selected.append(rec)
    old_front=json.loads(Path(previous.__file__).with_suffix('.json').read_text())['frontiers']
    improvements={};mapped=[];mapped_seen=set()
    for w in (None,43,44,45):
      for r in previous.frontier(w):
        key=(tuple(r['normalized_prefixes']),tuple(r['positive_scale_prefixes']),tuple(map(tuple,r['partition'])),r['anchor'])
        if key in mapped_seen:continue
        mapped_seen.add(key)
        mapped.append(record(base(key[0],key[1]),r['partition'],r['anchor']))
    mapped_improvements={}
    for key,rows in summaries.items():
        improvements[key]=[];mapped_improvements[key]=[]
        for cost,degree,w in rows:
            before=min((d for c,d,ww in old_front[key] if c<=cost),default=None)
            if before is not None and degree<before:
                improvements[key].append(dict(operations=cost,previous_bound=before,new_bound=degree,witnesses=w))
            mapped_before=min((r['polynomial']['degree_upper_bound'] for r in mapped
                if r['polynomial']['operations']<=cost and (key=='None' or r['certificate']['witnesses']==int(key))),default=None)
            if mapped_before is not None and degree<mapped_before:
                mapped_improvements[key].append(dict(operations=cost,mapped_bound=mapped_before,new_bound=degree,witnesses=w))
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_PRODUCT_SCALE_PARTITIONS',searches=studies,
        frontiers=summaries,native_bound_family_improvements=improvements,mapped_selected_parent_ledgers=mapped,
        mapped_selected_family_improvements=mapped_improvements,ledgers=ledgers,selected_sources=selected,
        complete_source_contexts=contexts,audit_totals=dict(totals),
        independent_search_validation=engine.small_search_audit(),rejected_callers=guard_audit(),
        scope='Exact finite disjoint-partition/anchor objective for sixteen mixed bases: eight use product253 at the final S bound, and eight retain the ordinary joint scale. Both bound interfaces and all witness strata. Guarded propagated bounds only; valid-slice within-base zero equality, cross-base and preceding-scale existential equivalence with fresh private native coordinates. No exact-degree or global-circuit optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print('Contexts',result['complete_source_contexts']);print(result['audit_totals'])
