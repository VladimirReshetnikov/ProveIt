"""Four complete U21 native bases and exact finite factor partitions.

Ordinary/normalized strong equations and ordinary/projected X bounds trade
operations, degree and50/51 witnesses. Program interfaces remain distinct.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_selector_sharing380 as parent
import neary_woods_universal_joint_and_coupled_partitions as optimizer

core=parent.core
execute=parent.execute
GAP='native__bound_beta';BOUND='native__bs_X_bound';INDEX='native__bs_packed'
S='counter_factored_inner';W='counter_partition_w'
STRONG='native__f_square_minus_one';DELTA='native__A';AUX='native__P17'


def closure(rows,roots):
    lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if isinstance(n,str) and n in lookup and n not in seen:
            seen.add(n);todo.extend(lookup[n])
    return [r for r in rows if r[0] in seen]


def polynomial_source(packet):
    if packet['partition_anchor'] is None:return core.ps.polynomial_source(packet)
    if len(packet['comparisons'])==1:
        return list(packet['source'])+[('counter_partition_output','-',packet['unit_register'],1)],'counter_partition_output'
    return core.units.polynomial_source(packet)


def degree_bound(packet):
    result=core.degree_bound(packet,sum_of_squares=packet['partition_anchor'] is None)
    return dict(result,group_degree_bounds=[sum(result['factor_degree_bounds'][i] for i in g) for g in packet['factor_partition']])


def grouped(scaffold,partition,anchor):
    nf=len(scaffold['unit_factors']);partition=[list(g) for g in partition]
    assert partition and all(partition) and sorted(i for g in partition for i in g)==list(range(nf))
    assert anchor is None or type(anchor) is int and 0<=anchor<len(partition)
    rows=list(scaffold['factor_source']);products=[]
    for j,g in enumerate(partition):
        product=scaffold['unit_factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name=f'counter_partition_group{j}_{k}';rows.append((name,'*',product,scaffold['unit_factors'][i]));product=name
        products.append(product)
    last=len(products)-1 if anchor is None else anchor
    pairs=list(scaffold['ordinary_comparisons'])+[(p,1) for j,p in enumerate(products) if j!=last]+[(products[last],1)]
    packet=core.ps.metadata(dict(scaffold,source=rows,comparisons=pairs,unit_register=products[last],
        group_products=products,factor_partition=partition,partition_anchor=anchor))
    original_grouping=partition==[list(range(nf))] and anchor==0
    original_base=packet['counter_strong_normalized'] and packet['counter_scale_projected']
    packet.update(identical_complete_polynomial=original_base and original_grouping,
        identical_positive_coordinates=original_base,
        identical_positive_zero_set=original_base,positive_zero_bijection=original_base,
        parent_identity_scope='These flags refer to the selector380 parent, not to different strong/scale bases.',
        identical_fixed_base_positive_zero_set=True)
    live=set(packet['parameters']+packet['auxiliaries'])|{n for n,_,_,_ in rows}
    for key in ('canonical_native_registers','private_restoration_coordinates'):
        if key in packet:packet[key]=[n for n in packet[key] if n in live]
    core.ps.checked_source(rows,packet['parameters'],packet['auxiliaries'])
    ss,out=polynomial_source(packet)
    assert len(closure(ss,[out]))==len(ss),'all emitted rows must reach the output'
    return packet


@lru_cache(None)
def base(normalized=True,scaled=True,program_radix=False):
    assert all(type(v) is bool for v in (normalized,scaled,program_radix))
    old=parent.build(program_radix=program_radix);rows=list(old['source'])
    factors=list(old['unit_factors']);pairs=[];aux=list(old['auxiliaries'])
    definitions={n:(o,a,b) for n,o,a,b in rows}
    assert definitions[STRONG]==('-','native__L16','native__normalized_strong_Q')
    assert definitions['native__R16']==('*',DELTA,'native__normalized_strong_Q')
    assert definitions[BOUND]==('+',S,GAP) and definitions['native__wn2']==('*',BOUND,'native__q')
    if not normalized:
        changes={STRONG:('-','native__L16',1),'native__R16':('*',DELTA,STRONG)}
        rows=[(n,*changes.get(n,(o,a,b))) for n,o,a,b in rows]
        factors.remove(STRONG);pairs.append(('native__ic22','native__R16'))
    if not scaled:
        changes={BOUND:('+',INDEX,GAP),'native__wn2':('*','native__q',W)}
        rows=[(n,*changes.get(n,(o,a,b))) for n,o,a,b in rows]
        pairs.append((BOUND,'native__wn2'));aux.append(W)
    rows=closure(rows,factors+[n for pair in pairs for n in pair])
    rows=core.ps.sort_source(rows,old['parameters']+aux)
    scaffold=dict(old,source=rows,factor_source=rows,unit_factors=factors,auxiliaries=aux,
        ordinary_comparisons=pairs,counter_factor_base=True,
        counter_strong_normalized=normalized,counter_scale_projected=scaled,
        normalized_strong=normalized,native_positive_scale=scaled,
        counter_factor_base_parent=old,
        identical_complete_polynomial=normalized and scaled,
        identical_positive_coordinates=normalized and scaled,
        positive_zero_set_scope='Within one fixed base all factor groupings have identical positive zeros on valid program/input slices. Cross-base strong extensions and scale-coordinate maps preserve the accepted outer relation.',
        historical_parent_metadata_scope='Stored normalization and scale parent packets refer to earlier sources; the active four-base recipe is specified here.')
    if not normalized:
        scaffold['normalized_strong_factor']=None
        scaffold['removed_strong_comparison']=None
    if not scaled:scaffold['positive_scale_removed_comparison']=None
    scaffold['positive_scale_domain']='Both bases prove X>r before typing; projected X=q*(S+beta), ordinary X=q*w=r+beta, with r=(q-1)*S and all supplied coordinates positive.'
    return grouped(scaffold,[list(range(len(factors)))],0)


def regroup(original,partition,anchor):
    assert original==base(original['counter_strong_normalized'],original['counter_scale_projected'],original['counter_program_radix']),'requires a complete canonical four-base source'
    return grouped(original,partition,anchor)


def record(packet):
    ss,out=polynomial_source(packet);c=Counter('M' if o=='*' else 'A' for _,o,_,_ in ss)
    degree=degree_bound(packet);nf=len(packet['unit_factors']);g=len(packet['factor_partition']);m=len(packet['ordinary_comparisons']);cc=len(packet['factor_source'])
    cost=cc+nf if m==0 and g==1 and packet['partition_anchor'] is not None else cc+nf+3*m-1+2*g
    assert cost==len(ss)
    assert packet['witnesses']==(50 if packet['counter_scale_projected'] else 51)
    return dict(normalized=packet['counter_strong_normalized'],scaled=packet['counter_scale_projected'],program_radix=packet['counter_program_radix'],
        partition=packet['factor_partition'],anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(ss),multiplications=c['M'],additions_subtractions=c['A'],degree_upper_bound=degree['degree_upper_bound'],exact_degree_claimed=False),
        degree=degree,factor_names=packet['unit_factors'],core_operations=cc,ordinary_comparisons=m)


@lru_cache(None)
def search(normalized,scaled,program_radix):
    p=base(normalized,scaled,program_radix);d=degree_bound(p);w=d['factor_degree_bounds'];r=d['maximum_residual_degree_bound']
    plans,statistics=optimizer.optimal_partitions(w,r)
    records=[]
    for plan in plans:
        packet=regroup(p,plan['partition'],plan['anchor']);rec=record(packet)
        assert rec['polynomial']['degree_upper_bound']==plan['degree_upper_bound']
        records.append(rec)
    floor=min(2*max(r,max(w)),max(w)+2*r,min(w)+2*max(r,max(w)))
    return dict(normalized=normalized,scaled=scaled,program_radix=program_radix,
        best_by_group_count=records,search_statistics=statistics,
        floor_certificate=dict(maximum_factor=max(w),minimum_factor=min(w),maximum_residual=r,lower_bound=floor))


@lru_cache(None)
def frontier(program_radix=False,witnesses=None):
    assert witnesses in (None,50,51)
    rows=[r for n in (False,True) for s in (False,True) if witnesses is None or (50 if s else 51)==witnesses
        for r in search(n,s,program_radix)['best_by_group_count']]
    rows.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']))
    result=[];best=float('inf')
    for row in rows:
        if row['polynomial']['degree_upper_bound']<best:result.append(row);best=row['polynomial']['degree_upper_bound']
    return result


def build(operations=380,*,program_radix=False,witnesses=None):
    plan=next(r for r in frontier(program_radix,witnesses) if r['polynomial']['operations']==operations)
    return regroup(base(plan['normalized'],plan['scaled'],program_radix),plan['partition'],plan['anchor'])


def base_maps(packet,seed,cases=24):
    old=packet['counter_factor_base_parent'];rng=random.Random(seed);totals=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        v={n:draw() for n in old['parameters']+old['auxiliaries']};e=execute(old['source'],v);lift=dict(v)
        if not packet['counter_strong_normalized']:lift['native__i']*=e[DELTA]
        if not packet['counter_scale_projected']:
            lift[W]=e[S]+v[GAP];lift[GAP]=e['native__q']*lift[W]-e[INDEX]
        before=execute(packet['source'],lift);at=lambda n:before[n] if isinstance(n,str) else n
        expected=[]
        for name in packet['unit_factors']:
            value=e[name]
            if name==AUX and not packet['counter_strong_normalized']:
                value+=e[DELTA]*(e[STRONG]-1)*e['native__aux_square_gap']
            assert before[name]==value;expected.append(value)
        residuals=[]
        if not packet['counter_strong_normalized']:residuals.append(e[DELTA]*(1-e[STRONG]))
        if not packet['counter_scale_projected']:residuals.append(0)
        assert [at(a)-at(b) for a,b in packet['ordinary_comparisons']]==residuals
        excluded={BOUND} if not packet['counter_scale_projected'] else set()
        if not packet['counter_strong_normalized']:
            excluded|={'native__ic2','native__ic22',STRONG,'native__R16','native__L17',AUX}
        assert all(before[n]==e[n] for n,_,_,_ in packet['factor_source'] if n not in excluded)
        if not signed:assert min(lift.values())>0;totals['positive_forward_coordinate_maps']+=1
        totals['complete_base_factor_and_residual_maps']+=1;totals['signed_assignments']+=signed
    return dict(totals)


def grouping_audit(original,partition,anchor,seed,cases=8):
    packet=regroup(original,partition,anchor);ss,out=polynomial_source(packet);rng=random.Random(seed);totals=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        v={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        e=execute(ss,v);before=execute(original['source'],v);at=lambda n:before[n] if isinstance(n,str) else n
        assert all(e[n]==before[n] for n,_,_,_ in original['factor_source'])
        products=[]
        for g in partition:
            value=1
            for i in g:value*=before[packet['unit_factors'][i]]
            products.append(value)
        assert products==[e[n] for n in packet['group_products']]
        expected=sum((at(a)-at(b))**2 for a,b in packet['ordinary_comparisons'])
        expected+=sum((x-1)**2 for j,x in enumerate(products) if j!=anchor)
        if anchor is not None:expected=products[anchor]*(1+expected)-1
        assert e[out]==expected
        totals['complete_same_base_factor_group_output_checks']+=1;totals['signed_assignments']+=signed
    return dict(totals)


def guards():
    p=base();bad=[dict(p,parameters=['bad']),dict(p,source=p['source'][:-1]),dict(p,interfaces={'hidden':GAP})]
    for v in bad:
        try:regroup(v,[list(range(len(p['unit_factors'])))],0)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('noncanonical source accepted')
    for partition,anchor in (([[0]],0),([[]],0),([list(range(len(p['unit_factors'])))],2)):
        try:regroup(p,partition,anchor)
        except AssertionError:pass
        else:raise AssertionError('invalid grouping accepted')
    return len(bad)+3


def verify():
    studies=[];bases=[];selected=[];totals=Counter();frontiers={}
    for pr in (False,True):
      for n in (False,True):
       for s in (False,True):
        study=search(n,s,pr);studies.append(study);p=base(n,s,pr);rec=record(p)
        rec['audit']=base_maps(p,380040+len(bases));totals.update(rec['audit']);bases.append(rec)
        nf=len(p['unit_factors']);groups=[list(range(j,nf,3)) for j in range(3)]
        for anchor in (None,1):totals.update(grouping_audit(p,groups,anchor,380500+len(bases)))
      for witnesses in (None,50,51):
        plans=frontier(pr,witnesses);frontiers[f'{pr}/{witnesses}']=[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in plans]
      seen=set()
      for witnesses in (None,50,51):
       for r in frontier(pr,witnesses):
        key=(r['normalized'],r['scaled'],tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);p=base(key[0],key[1],pr);packet=regroup(p,r['partition'],r['anchor']);ss,out=polynomial_source(packet);rec=record(packet)
        rec['audit']=grouping_audit(p,r['partition'],r['anchor'],381000+len(selected));totals.update(rec['audit'])
        rec.update(source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest());selected.append(rec)
    assert frontiers['False/None']==[(380,21549,50),(382,18951,50),(384,13456,50),(385,9114,51),(387,6512,51),(389,4542,51),(391,3896,51)]
    floors={}
    for pr in (False,True):
      for witnesses in (None,50,51):
        eligible=[s for s in studies if s['program_radix']==pr and (witnesses is None or (50 if s['scaled'] else 51)==witnesses)]
        lower=min(s['floor_certificate']['lower_bound'] for s in eligible)
        endpoint=frontier(pr,witnesses)[-1]
        assert endpoint['polynomial']['degree_upper_bound']==lower
        floors[f'{pr}/{witnesses}']=dict(lower_bound=lower,attained_operations=endpoint['polynomial']['operations'])
    return dict(status='PASS_KOREC_PACKED_FACTOR_PARTITIONS',studies=studies,bases=bases,
        frontiers=frontiers,attained_floor_certificates=floors,selected_sources=selected,audit_totals=dict(totals),rejected_callers=guards(),
        independent_small_search_validation=optimizer.small_exhaustive_checks(),
        scope='Four complete strong/scale bases per fixed program interface, exact finite disjoint partitions and SOS/anchor finalizers. Same supplied positive zeros within each base on valid slices; accepted outer equivalence across bases through scale maps and canonical strong extensions. Guarded propagated bounds only.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['audit_totals'])
