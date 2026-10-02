"""Exact 32-base C2 transport/query factor partitions on valid program slices.

All individual factors have positive sign on those slices. Same-base grouping
preserves supplied positive zeros; initial/global shifts and fresh strong
extensions have their separate cross-base scopes. Degrees are upper bounds.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path
import random

import tseytin_cross_offset_factor_partitions as previous
import tseytin_upper_transport_unit381 as upper_parent
import tseytin_lower_transport_unit380 as lower_parent
import tseytin_query_unit378 as query_parent

scale, execute, closure = previous.scale, previous.execute, previous.closure
optimizer = previous.previous.optimizer
FIELDS = ('normalized','global_unit','upper','lower','query')
EXPECTED = [(378,4713),(380,4147),(381,4140),(382,2900),(384,2210),(386,1664)]


def _flags(packet):
    flags = tuple(packet[k] for k in FIELDS)
    assert all(type(v) is bool for v in flags)
    return flags


def rewrite_base(old, *, upper=True, lower=True, query=True):
    assert all(type(v) is bool for v in (upper,lower,query))
    normalized, global_unit = old['word_strong_normalized'], old['global_unit']
    assert type(normalized) is bool and type(global_unit) is bool
    assert old == previous.base(normalized,global_unit), 'complete canonical cross-offset factor base required'
    rows = list(old['source']); before = {n:(o,a,b) for n,o,a,b in rows}
    assert len(before) == len(rows)
    assert all(before.get(n) == v for n,v in upper_parent.REQUIRED.items())
    assert all(before.get(n) == v for n,v in lower_parent.REQUIRED.items())
    assert not any(upper_parent.PAIR[0] in (a,b) for n,o,a,b in rows)
    assert upper_parent.PAIR[0] not in previous.local.leaves(old['interfaces'])
    assert {n for n,o,a,b in rows if 'c2_initial' in (a,b)} == lower_parent.INITIAL_CONSUMERS
    assert not any(query_parent.PAIR[0] in (a,b) for n,o,a,b in rows)
    assert old['interfaces']['initial'] == 'c2_initial' and 'initial_minus_one' not in old['interfaces']
    factors, pairs = list(old['unit_factors']), list(old['ordinary_comparisons'])
    for pair in (upper_parent.PAIR,lower_parent.PAIR,query_parent.PAIR): assert pairs.count(pair) == 1
    added = [upper_parent.TRANSPORT,lower_parent.TRANSPORT,query_parent.QUERY]
    assert not set(added)&(set(before)|set(old['parameters']+old['auxiliaries']))
    if upper:
        rows = [r for r in rows if r[0] != upper_parent.PAIR[0]]
        rows.append((upper_parent.TRANSPORT,'-',upper_parent.PAIR[1],upper_parent.UPDATE))
        factors.append(upper_parent.TRANSPORT); pairs.remove(upper_parent.PAIR)
    if lower:
        rows = [(n,o,a,b+lower_parent.DENOMINATOR) if n == query_parent.PAIR[0] else (n,o,a,b) for n,o,a,b in rows]
        rows.append((lower_parent.TRANSPORT,'-',lower_parent.PAIR[1],lower_parent.PAIR[0]))
        factors.append(lower_parent.TRANSPORT); pairs.remove(lower_parent.PAIR)
    if query:
        rows = [(n,o,a,b-1) if n == query_parent.PAIR[0] else (n,o,a,b) for n,o,a,b in rows]
        rows.append((query_parent.QUERY,'-',*query_parent.PAIR))
        factors.append(query_parent.QUERY); pairs.remove(query_parent.PAIR)
    rows = scale.sort_source(rows,old['parameters']+old['auxiliaries'])
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    actual = {n:(o,a,b) for n,o,a,b in rows}
    # Establish actual local proof cones, not inherited flags alone.
    native = lambda by:{n:v for n,v in by.items() if n.startswith(('and__','exp__'))}
    assert native(actual) == native(before)
    rename = lambda n:('exp__'+n if isinstance(n,str) and n != 'x' else n)
    exponent = query_parent.exponent.build()
    exp_rows = {rename(n):(o,rename(a),rename(b)) for n,o,a,b in closure(exponent['source'],exponent['unit_factors'])}
    assert len(exponent['source']) == 51 and len(exp_rows) == 46
    assert all(actual.get(n) == v for n,v in exp_rows.items())
    power_factors = [rename(n) for n in exponent['unit_factors']]
    assert all(f in factors for f in power_factors)
    roots = ['global_lhs__40','P__30','joined_H__287','joined_M__293','joined_Z__294']
    cone = lambda source:{n:(o,a,b) for n,o,a,b in closure(source,roots)}
    assert cone(rows) == cone(old['source'])
    assert actual[query_parent.PAIR[0]] == ('-','query_last_product',lower_parent.QUERY_CONSTANT+int(lower)*query_parent.D-int(query))
    assert actual['query_scaled_word'] == ('*',query_parent.D,'c2_initial')
    assert len(closure(rows,factors+[v for pair in pairs for v in pair])) == len(rows)
    interface = deepcopy(old['interfaces'])
    if lower:
        del interface['initial']; interface['initial_minus_one'] = 'c2_initial'
    recipe = old['program_recipe']
    recipe += (' The supplied c2_initial is enc_new(query+#)-1; the numerator is N-d.' if lower else
               ' The supplied c2_initial is enc_new(query+#); the numerator is N.')
    if query: recipe += ' The active numerator additionally includes +1; query_unit=1 restores that exact query.'
    flags = dict(zip(FIELDS,(normalized,global_unit,upper,lower,query)))
    return dict(**flags,word_strong_normalized=normalized,source=rows,factor_source=rows,
        parameters=list(old['parameters']),auxiliaries=list(old['auxiliaries']),
        unit_factors=factors,power_factors=power_factors,ordinary_comparisons=pairs,
        interfaces=interface,program_recipe=recipe,letter_codes=deepcopy(old['letter_codes']),tiles=deepcopy(old['tiles']),
        positive_integer_domain=True,transport_query_factor_base=True,
        global_unit_register=previous.previous.G if global_unit else None,
        upper_transport_register=upper_parent.TRANSPORT if upper else None,
        lower_transport_register=lower_parent.TRANSPORT if lower else None,
        query_unit_register=query_parent.QUERY if query else None,
        literal_initial_relation='literal encoding = c2_initial + '+str(int(lower)),
        query_numerator_offset=-int(lower)*query_parent.D+int(query),
        source_verified_contract=dict(parent=deepcopy(old['source_verified_contract']),
            native_and_exponent_rows=len(native(actual)),unchanged_pretyping_rows=len(cone(rows)),
            complete_exponent_factor_cone_rows=len(exp_rows),original_exponent_certificate_rows=51,power_factors=power_factors,
            initial_consumers=sorted(lower_parent.INITIAL_CONSUMERS),
            all_factors_positive_scope='valid recompiled program slices only'),
        projection='Within a base, all groupings have equal supplied positive zeros on valid recompiled program slices. Lower choices shift the initial coordinate, global choices shift their slack, and strong choices use fresh five-coordinate extensions preserving the outer projection. No cross-base off-zero polynomial identity is asserted.')


@lru_cache(None)
def _base(normalized,global_unit,upper,lower,query):
    return rewrite_base(previous.base(normalized,global_unit),upper=upper,lower=lower,query=query)


def base(normalized=True,global_unit=True,upper=True,lower=True,query=True):
    assert all(type(v) is bool for v in (normalized,global_unit,upper,lower,query))
    return deepcopy(_base(normalized,global_unit,upper,lower,query))


def grouped(original,partition,anchor):
    assert original == base(*_flags(original)), 'complete canonical transport/query factor base required'
    partition = [list(g) for g in partition]; nf = len(original['unit_factors'])
    assert partition and all(partition)
    assert all(type(i) is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g) == list(range(nf))
    assert anchor is None or (type(anchor) is int and 0 <= anchor < len(partition))
    rows, products = list(original['source']),[]
    names = {n for n,o,a,b in rows}|set(original['parameters']+original['auxiliaries'])
    for j,g in enumerate(partition):
        value = original['unit_factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name = f'tq_group_{j}_{k}'; assert name not in names; names.add(name)
            rows.append((name,'*',value,original['unit_factors'][i])); value = name
        products.append(value)
    last = len(products)-1 if anchor is None else anchor
    comparisons = original['ordinary_comparisons']+[(v,1) for j,v in enumerate(products) if j != last]+[(products[last],1)]
    p = scale.metadata(dict(deepcopy(original),source=rows,comparisons=comparisons,
        unit_register=products[last],group_products=products,factor_partition=partition,partition_anchor=anchor,
        transport_query_factor_partition=True,identical_fixed_base_positive_zero_set=True,
        positive_zero_equality_scope='valid recompiled program slices only',
        cross_base_integer_polynomial_identity_claimed=False))
    scale.checked_source(rows,p['parameters'],p['auxiliaries'])
    return p


def checked_packet(packet):
    assert packet == grouped(base(*_flags(packet)),packet['factor_partition'],packet['partition_anchor']), 'complete canonical grouped packet required'


def polynomial_source(packet):
    checked_packet(packet)
    if packet['partition_anchor'] is not None and len(packet['comparisons']) == 1:
        assert packet['comparisons'] == [(packet['unit_register'],1)]
        assert not packet['ordinary_comparisons'] and len(packet['factor_partition']) == 1
        name = 'tq_direct_output'; assert name not in {n for n,o,a,b in packet['source']}
        return list(packet['source'])+[(name,'-',packet['unit_register'],1)],name
    return previous.previous.word.norms.polynomial_source(packet,sum_of_squares=packet['partition_anchor'] is None)


def degree_dictionary(packet):
    """Low-level guarded norm propagation; public degree_bound checks the full packet."""
    return previous.degree_dictionary(packet)


def degree_bound(packet):
    checked_packet(packet); d = degree_dictionary(packet)
    at = lambda n:d[n] if isinstance(n,str) else 0
    weights = [at(n) for n in packet['unit_factors']]
    r = max((max(at(a),at(b)) for a,b in packet['ordinary_comparisons']),default=0)
    groups = [sum(weights[i] for i in g) for g in packet['factor_partition']]
    assert groups == [at(n) for n in packet['group_products']]
    a = packet['partition_anchor']
    bound = 2*max([r]+groups) if a is None else groups[a]+2*max([r]+[v for j,v in enumerate(groups) if j != a])
    return dict(degree_upper_bound=bound,factor_degree_bounds=weights,
        maximum_original_residual_degree_bound=r,group_degree_bounds=groups,exact_degree_claimed=False)


def ledger(packet):
    rows,out = polynomial_source(packet); counts = Counter(o for n,o,a,b in rows)
    c,n,m,g = len(packet['factor_source']),len(packet['unit_factors']),len(packet['ordinary_comparisons']),len(packet['factor_partition'])
    special = packet['partition_anchor'] is not None and m == 0 and g == 1
    assert len(rows) == c+n+3*m-1+2*g-int(special)
    assert len(closure(rows,[out])) == len(rows)
    assert degree_dictionary(dict(packet,source=rows))[out] == degree_bound(packet)['degree_upper_bound']
    return dict(**dict(zip(FIELDS,_flags(packet))),partition=packet['factor_partition'],anchor=packet['partition_anchor'],
        core_operations=c,ordinary_comparisons=m,factor_names=packet['unit_factors'],
        empty_residual_product_minus_one=special,
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],**degree_bound(packet)))


@lru_cache(None)
def _search(normalized,global_unit,upper,lower,query):
    original = base(normalized,global_unit,upper,lower,query); n = len(original['unit_factors'])
    degree = degree_bound(grouped(original,[list(range(n))],0))
    weights,r = degree['factor_degree_bounds'],degree['maximum_original_residual_degree_bound']
    plans,statistics = optimizer.optimal_partitions(weights,r); records = []
    for p in plans:
        record = ledger(grouped(original,p['partition'],p['anchor']))
        assert record['polynomial']['degree_upper_bound'] == p['degree_upper_bound']
        records.append(record)
    floor,maskbest = 2*max([r]+weights),None
    for mask in range(1,1 << n):
        value = sum(w for i,w in enumerate(weights) if mask >> i & 1)+2*max([r]+[w for i,w in enumerate(weights) if not(mask >> i & 1)])
        if value < floor: floor,maskbest = value,mask
    assert min(v['polynomial']['degree_upper_bound'] for v in records) == floor
    return dict(**dict(zip(FIELDS,(normalized,global_unit,upper,lower,query))),statistics=statistics,
        best_by_group_count=records,floor_certificate=dict(lower_bound=floor,anchor_mask=maskbest,
            anchor_masks_checked=(1 << n)-1,
            attained_operations=min(v['polynomial']['operations'] for v in records if v['polynomial']['degree_upper_bound']==floor)))


def search(normalized=True,global_unit=True,upper=True,lower=True,query=True):
    assert all(type(v) is bool for v in (normalized,global_unit,upper,lower,query))
    return deepcopy(_search(normalized,global_unit,upper,lower,query))


def frontier(*,normalized=None,global_unit=None,upper=None,lower=None,query=None):
    flags = (normalized,global_unit,upper,lower,query)
    assert all(v is None or type(v) is bool for v in flags)
    records = [r for selected in product(*[((False,True) if v is None else (v,)) for v in flags])
               for r in _search(*selected)['best_by_group_count']]
    result,best = [],float('inf')
    for r in sorted(records,key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'])):
        if r['polynomial']['degree_upper_bound'] < best:
            result.append(deepcopy(r)); best = r['polynomial']['degree_upper_bound']
    return result


def build(operations=386,*,normalized=None,global_unit=None,upper=None,lower=None,query=None):
    assert type(operations) is int and operations > 0
    r = next(r for r in frontier(normalized=normalized,global_unit=global_unit,upper=upper,lower=lower,query=query)
             if r['polynomial']['operations'] == operations)
    return grouped(base(*_flags(r)),r['partition'],r['anchor'])


def grouping_audit(packet,cases=4,seed=378386):
    rows,out = polynomial_source(packet); rng,counts = random.Random(seed),Counter()
    for case in range(cases):
        signed = case >= cases//2
        draw = lambda:rng.randrange(-2,3) if signed else rng.randrange(1,3)
        v = {n:draw() for n in packet['parameters']+packet['auxiliaries']}
        if case == 0: v.update({f'Shat{i}':1 for i in range(24)}); counts['zero_selector_cases'] += 1
        e = execute(rows,v); old = execute(packet['factor_source'],v)
        assert all(e[n] == old[n] for n,o,a,b in packet['factor_source'])
        groups = [prod(old[packet['unit_factors'][i]] for i in g) for g in packet['factor_partition']]
        assert groups == [e[n] for n in packet['group_products']]
        at = lambda n:old[n] if isinstance(n,str) else n
        a = packet['partition_anchor']
        S = sum((at(u)-at(w))**2 for u,w in packet['ordinary_comparisons'])+sum((g-1)**2 for j,g in enumerate(groups) if j != a)
        assert e[out] == (S if a is None else groups[a]*(1+S)-1)
        counts['complete_core_group_and_manual_outputs'] += 1; counts['signed_outputs'] += signed
    return dict(counts)


def coordinate_audit():
    counts,rng = Counter(),random.Random(378380383)
    for flags in product((False,True),repeat=5):
        n,g,u,l,q = flags; p = base(*flags); old = previous.base(n,g)
        for case in range(8):
            signed = case >= 4
            draw = lambda:rng.randrange(-2,3) if signed else rng.randrange(1,4)
            v = {name:draw() for name in p['parameters']+p['auxiliaries']}
            image = dict(v,c2_initial=v['c2_initial']+int(l))
            current = execute(p['source'],v); past = execute(old['source'],image)
            delta = {'V_lhs__153':int(l),'query_scaled_word':int(l)*query_parent.D,
                     'query_numerator':int(l)*query_parent.D-int(q)}
            for name,o,a,b in old['source']:
                if u and name == 'U_lhs__151': assert past[name] == current[upper_parent.UPDATE]+1
                else: assert past[name] == current[name]+delta.get(name,0),name
            if u: assert current[upper_parent.TRANSPORT] == past['U_rhs__155']-past['U_lhs__151']+1
            if l: assert current[lower_parent.TRANSPORT] == past['V_rhs__157']-past['V_lhs__153']+1
            if q: assert current[query_parent.QUERY] == past['query_numerator']-past['query_scaled_word']+1
            counts['complete_transport_query_register_maps'] += 1; counts['signed_transport_query_maps'] += signed
    for g,u,l,q in product((False,True),repeat=4):
        norm,ordinary = base(True,g,u,l,q),base(False,g,u,l,q)
        changed = {'and__ic2','and__ic22',previous.previous.STRONG,'and__R16','and__L17','and__P17'}
        for case in range(8):
            signed = case >= 4; draw = lambda:rng.randrange(-2,3) if signed else rng.randrange(1,4)
            v = {n:draw() for n in norm['parameters']+norm['auxiliaries']}
            a = execute(norm['source'],v); b = execute(ordinary['source'],dict(v,**{'and__i':a['and__A']*v['and__i']}))
            D,N = a['and__A'],a[previous.previous.STRONG]
            assert b['and__ic22']-b['and__R16'] == D*(1-N)
            assert b['and__P17']-a['and__P17'] == D*(N-1)*a['and__aux_square_gap']
            assert all(a[n] == b[n] for n,o,v,w in ordinary['source'] if n not in changed)
            counts['complete_strong_register_corrections'] += 1; counts['signed_strong_maps'] += signed
    for n,u,l,q in product((False,True),repeat=4):
        new,old = base(n,True,u,l,q),base(n,False,u,l,q)
        for case in range(8):
            signed = case >= 4; draw = lambda:rng.randrange(-2,3) if signed else rng.randrange(1,4)
            v = {name:draw() for name in new['parameters']+new['auxiliaries']}
            a = execute(new['source'],v); b = execute(old['source'],dict(v,global_bound=v['global_bound']+1))
            assert all(a[name] == b[name] for name,o,x,y in old['source'] if name != 'global_lhs__40')
            assert b['global_lhs__40'] == a['global_lhs__40']+1
            counts['complete_global_slack_maps'] += 1; counts['signed_global_maps'] += signed
    return dict(counts)


def canonical_audit():
    counts = Counter()
    for global_unit in (False,True):
        for upper,lower,query in ((False,False,False),(True,False,False),(True,True,False),(True,True,True)):
            parent = query_parent if query else lower_parent if lower else upper_parent if upper else previous.local
            direct = parent.build(global_unit=global_unit)
            original = base(True,global_unit,upper,lower,query)
            roots = direct['word_factors']+direct['power_factors']+[v for pair in direct['ordinary_comparisons'] for v in pair]
            assert {n:(o,a,b) for n,o,a,b in closure(direct['source'],roots)} == {n:(o,a,b) for n,o,a,b in original['source']}
            for sos in (False,True):
                p = grouped(original,[list(range(len(original['unit_factors'])))],None if sos else 0)
                rows,out = polynomial_source(p); before,target = parent.polynomial_source(direct,sum_of_squares=sos)
                for k in range(8):
                    values = {n:(k+i)%5-2 for i,n in enumerate(p['parameters']+p['auxiliaries'])}
                    assert execute(rows,values)[out] == execute(before,values)[target]
                    counts['complete_canonical_parent_outputs'] += 1
                counts['canonical_source_cones_and_finalizers'] += 1
    return dict(counts)


def bell_audit():
    def partitions(n):
        if n == 0: yield []; return
        for p in partitions(n-1):
            yield p+[[n-1]]
            for i in range(len(p)):
                yield [g+[n-1] if j==i else list(g) for j,g in enumerate(p)]
    counts = Counter()
    for weights in ([2,3,7],[1,4,5,8],[2,2,3,7,11],[1,3,4,6,9,12]):
      for residual in (0,3,13):
        best = {}; plans,_ = optimizer.optimal_partitions(weights,residual)
        for p in partitions(len(weights)):
            w = [sum(weights[i] for i in g) for g in p]; k = len(w)
            values = [2*max([residual]+w)]+[v+2*max([residual]+[z for j,z in enumerate(w) if j != a]) for a,v in enumerate(w)]
            best[k] = min(best.get(k,float('inf')),min(values))
            counts['bell_partitions'] += 1; counts['bell_finalizer_objectives'] += len(values)
        assert [p['degree_upper_bound'] for p in plans] == [best[k] for k in range(1,len(weights)+1)]
        counts['bell_contexts'] += 1
    return dict(counts)


def guards():
    count = 0
    def reject(call):
        nonlocal count
        try: call()
        except (AssertionError,KeyError): count += 1
        else: raise AssertionError('malformed caller accepted')
    old = previous.base()
    for key,value in [('source',old['source'][:-1]),('interfaces',{}),('program_recipe','wrong'),
                      ('source_verified_contract',{}),('unit_factors',[]),('extra_export','U_lhs__151')]:
        reject(lambda key=key,value=value:rewrite_base(dict(old,**{key:value})))
    for flags in product((False,True),repeat=5):
        b = base(*flags); nf = len(b['unit_factors']); p = grouped(b,[list(range(nf))],0)
        for key,value in [('source',p['source'][:-1]),('interfaces',{}),('query_numerator_offset',123),
                          ('program_recipe','wrong'),('literal_initial_relation','wrong')]:
            reject(lambda key=key,value=value:polynomial_source(dict(p,**{key:value})))
        reject(lambda:degree_bound(dict(p,source_verified_contract={})))
        for partition,anchor in [([[0]],0),([[]],None),([list(range(nf))],True),
                                 ([list(range(nf))],1),([list(range(nf-1))+[True]],None)]:
            reject(lambda partition=partition,anchor=anchor:grouped(b,partition,anchor))
    for key in FIELDS:
        reject(lambda key=key:base(**{key:1})); reject(lambda key=key:search(**{key:1}))
        reject(lambda key=key:frontier(**{key:1}))
    reject(lambda:build(True))
    return count


def verify():
    studies = [search(*flags) for flags in product((False,True),repeat=5)]
    totals,records = Counter(),[]
    for study in studies:
        original = base(*_flags(study))
        for r in study['best_by_group_count']:
            p = grouped(original,r['partition'],r['anchor']); rec = ledger(p)
            rec['audit'] = grouping_audit(p,seed=378000+len(records)); totals.update(rec['audit']); records.append(rec)
    assert len(records) == 432
    front = frontier(); assert [(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in front] == EXPECTED
    assert min(s['floor_certificate']['lower_bound'] for s in studies) == 1664
    extra = []
    for flags in product((False,True),repeat=5):
        original = base(*flags); n = len(original['unit_factors'])
        part = [list(range(n-1,-1,-1))[j::3] for j in range(3)]
        for a in (None,2):
            p = grouped(original,part,a); r = ledger(p); r['audit'] = grouping_audit(p,seed=386000+len(extra))
            totals.update(r['audit']); extra.append(r)
    special = base(); special_records = []
    for a in (0,None):special_records.append(ledger(grouped(special,[list(range(len(special['unit_factors'])))],a)))
    assert [r['polynomial']['operations'] for r in special_records] == [378,379]
    filters = {f'{key}={value}':[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in frontier(**{key:value})]
               for key in FIELDS for value in (False,True)}
    examples = []
    for rec in front:
        p = grouped(base(*_flags(rec)),rec['partition'],rec['anchor']); rows,out = polynomial_source(p)
        examples.append(dict(record=rec,source=rows,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
            comparisons=p['comparisons'],interfaces=p['interfaces'],program_recipe=p['program_recipe'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()))
    return dict(status='PASS_TSEYTIN_TRANSPORT_QUERY_FACTOR_PARTITIONS',bases=32,optimal_ledgers=len(records),
        studies=studies,optimal_records=records,additional_plans=extra,frontier=front,filtered_frontiers=filters,
        empty_residual_finalizers=special_records,full_sources=examples,output_audit=dict(totals),
        coordinate_audit=coordinate_audit(),canonical_audit=canonical_audit(),bell_audit=bell_audit(),
        residue_audit=query_parent.residue_audit(),rejected_callers=guards(),
        scope='Exactly32 selected source bases and all factor partitions/anchors. Positive-zero equality within a base on valid recompiled program slices; lower/global coordinate shifts and cross-strong fresh five-coordinate outer extensions retain distinct scopes. Propagated degree bounds only; finite-family floor1664. No full compiled Pell-zero fixture.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write',action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status']); print(result['output_audit']); print(result['coordinate_audit']); print(result['bell_audit'])
    print([(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in result['frontier']])
