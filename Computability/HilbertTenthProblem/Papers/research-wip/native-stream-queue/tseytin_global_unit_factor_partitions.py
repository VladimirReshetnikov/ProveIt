"""Exact four-base factor partitions around the Tseytin global-unit change.

The global-unit theorem supplies every individual factor's positive sign
on valid recompiled program slices. Grouping preserves the full supplied
positive zeros within a base; ordinary/normalized strong bases instead
have positive existential extensions. Degrees are propagated bounds.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_global_bound_unit385 as parent
import tseytin_permuted_factor_partitions as previous
import neary_woods_universal_joint_and_coupled_partitions as optimizer

G = parent.G
STRONG, QSTRONG = previous.STRONG, previous.QSTRONG
scale, word, execute = parent.scale, previous.word, parent.execute
closure = previous.closure
EXPECTED = [(385,4714),(386,4134),(387,4132),(388,2900),(390,2210),(392,1664)]


def source_contract(old, global_unit=True):
    """Re-establish the exact current local theorem ports, including G.

    Historical metadata is not used as a substitute for source equality.
    The reference's native, exponent and pretyping contracts are themselves
    guarded against the frozen computed-field/zero-a ancestry.
    """
    assert type(global_unit) is bool
    (parent if global_unit else parent.parent).checked_packet(old)
    assert old['merge_units'] is True
    reference = previous.parent.build()
    ancestral = previous.source_contract(reference)
    actual = {n:(o,a,b) for n,o,a,b in old['source']}
    past = {n:(o,a,b) for n,o,a,b in reference['source']}
    native = lambda rows:{n:v for n,v in rows.items() if n.startswith(('and__','exp__'))}
    assert native(actual) == native(past)
    roots = ['global_lhs__40','P__30','joined_H__287','joined_M__293','joined_Z__294']
    cone = lambda rows,rs:{n:(o,a,b) for n,o,a,b in closure(rows,rs)}
    oldcone = cone(reference['source'],roots)
    assert cone(old['source'],roots) == oldcone
    if global_unit:
        assert actual[G] == ('-','P__30','global_lhs__40')
        assert cone(old['source'],roots+[G]) == dict(oldcone,**{G:actual[G]})
    else:
        assert G not in actual
    assert actual['global_lhs__40'] == ('+','global_bound','global_sum__39')
    assert {n for n,_,a,b in old['source'] if 'global_bound' in (a,b)} == {'global_lhs__40'}
    for key in ('parameters','auxiliaries','power_factors','letter_codes','tiles','program_recipe'):
        assert old[key] == reference[key], key
    assert old['word_factors'] == reference['word_factors']+([G] if global_unit else [])
    assert old['ordinary_comparisons'] == [p for p in reference['ordinary_comparisons']
                                            if not global_unit or p != parent.GLOBAL_PAIR]
    if global_unit: assert old['global_unit_register'] == G
    assert len(old['auxiliaries']) == 62
    assert not {'and__F0','and__F1','and__F2','and__bs_q'}&set(old['auxiliaries'])
    return dict(native_and_exponent_rows=len(native(actual)),
                unchanged_pretyping_rows=len(oldcone),additional_pretyping_factor=G if global_unit else None,
                ancestry_contract=ancestral,checksum_fixed_one=True,
                computed_truth_fields=True,native_inner_bound=True)


@lru_cache(None)
def _base(normalized, global_unit):
    assert type(normalized) is bool and type(global_unit) is bool
    old = (parent if global_unit else parent.parent).build()
    contract = source_contract(old, global_unit)
    rows = list(old['source'])
    previous._strong_guard(rows)
    factors = list(old['word_factors'])+list(old['power_factors'])
    pairs = list(old['ordinary_comparisons'])
    assert len(factors) == 12+int(global_unit) and len(pairs) == 4-int(global_unit)
    if not normalized:
        changes = {STRONG:('-','and__L16',1),'and__R16':('*','and__A',STRONG)}
        rows = [(n,*changes.get(n,(o,a,b))) for n,o,a,b in rows]
        factors.remove(STRONG)
        pairs.append(('and__ic22','and__R16'))
    rows = closure(rows,factors+[v for pair in pairs for v in pair])
    rebuilt = {'and__'+n for n in ('f','i','j','o','y_aux')}
    deps = {n:({n} if n in rebuilt else set()) for n in old['parameters']+old['auxiliaries']}
    dep = lambda v:deps[v] if isinstance(v,str) else set()
    for n,_,a,b in rows: deps[n] = dep(a)|dep(b)
    stable = ['and__q','and__bs_packed','and__factored_index_inner','and__wn2','and__sn2',
              'and__R12','and__R10a','and__root_base','and__R15','and__first_unit',
              'and__index_unit','P__30','global_lhs__40']+([G] if global_unit else [])
    stable += old['power_factors']+[v for pair in old['ordinary_comparisons'] for v in pair]
    assert all(not dep(v)&rebuilt for v in stable)
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    assert len(rows) == 360+int(normalized)+int(global_unit)
    return dict(source=rows,factor_source=rows,parameters=list(old['parameters']),
                auxiliaries=list(old['auxiliaries']),unit_factors=factors,
                ordinary_comparisons=pairs,word_strong_normalized=normalized,global_unit=global_unit,
                interfaces=deepcopy(old['interfaces']),program_recipe=old['program_recipe'],
                letter_codes=deepcopy(old['letter_codes']),tiles=deepcopy(old['tiles']),
                positive_integer_domain=True,global_unit_factor_base=True,
                source_verified_contract=contract,global_unit_register=G if global_unit else None,
                semantic_reference=('global-bound-unit385' if global_unit else 'shared-offset386')+' on valid recompiled program slices',
                projection='All groupings in one fixed base have identical supplied positive zeros on valid program slices; changing global treatment shifts its positive slack by one, while changing strong treatment uses fresh five-coordinate auxiliary extensions.')


def base(normalized=True, global_unit=True):
    return deepcopy(_base(normalized, global_unit))


def grouped(original,partition,anchor):
    assert original == base(original['word_strong_normalized'],original['global_unit']), 'complete canonical factor base required'
    nf = len(original['unit_factors'])
    partition = [list(g) for g in partition]
    assert partition and all(partition)
    assert all(type(i) is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g) == list(range(nf))
    assert anchor is None or (type(anchor) is int and 0 <= anchor < len(partition))
    rows,products = list(original['source']),[]
    names = {n for n,_,_,_ in rows}|set(original['parameters']+original['auxiliaries'])
    for j,g in enumerate(partition):
        value = original['unit_factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name = f'global_partition_group{j}_{k}'
            assert name not in names
            names.add(name)
            rows.append((name,'*',value,original['unit_factors'][i]))
            value = name
        products.append(value)
    last = len(products)-1 if anchor is None else anchor
    comparisons = list(original['ordinary_comparisons'])+[(v,1) for j,v in enumerate(products) if j != last]+[(products[last],1)]
    packet = scale.metadata(dict(original,source=rows,comparisons=comparisons,
        unit_register=products[last],group_products=products,
        factor_partition=partition,partition_anchor=anchor,
        identical_complete_polynomial_to_selected_parent=original['word_strong_normalized'] and partition==[list(range(nf))] and anchor==0,
        identical_fixed_base_positive_zero_set=True,
        positive_zero_equality_scope='valid recompiled program slices only',
        global_unit_factor_partition=True))
    scale.checked_source(rows,packet['parameters'],packet['auxiliaries'])
    return packet


def checked_packet(packet):
    assert packet == grouped(base(packet['word_strong_normalized'],packet['global_unit']),packet['factor_partition'],packet['partition_anchor']), 'complete canonical grouped packet required'


def polynomial_source(packet):
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=packet['partition_anchor'] is None)


def degree_dictionary(packet):
    """Low-level guarded norm degree propagator, not a canonical-packet API."""
    return previous.degree_dictionary(packet)


def degree_bound(packet):
    checked_packet(packet)
    degrees = degree_dictionary(packet)
    d = lambda v:degrees[v] if isinstance(v,str) else 0
    weights = [d(f) for f in packet['unit_factors']]
    residual = max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons'])
    groups = [sum(weights[i] for i in g) for g in packet['factor_partition']]
    assert groups == [d(p) for p in packet['group_products']]
    anchor = packet['partition_anchor']
    bound = 2*max([residual]+groups) if anchor is None else groups[anchor]+2*max([residual]+[v for j,v in enumerate(groups) if j != anchor])
    return dict(degree_upper_bound=bound,factor_degree_bounds=weights,
                maximum_original_residual_degree_bound=residual,
                group_degree_bounds=groups,exact_degree_claimed=False)


def ledger(packet):
    rows,out = polynomial_source(packet)
    counter = Counter(o for _,o,_,_ in rows)
    nf,g,m,c = len(packet['unit_factors']),len(packet['factor_partition']),len(packet['ordinary_comparisons']),len(packet['factor_source'])
    assert len(rows) == c+nf+3*m-1+2*g
    assert len(closure(rows,[out])) == len(rows)
    return dict(normalized=packet['word_strong_normalized'],global_unit=packet['global_unit'],partition=packet['factor_partition'],anchor=packet['partition_anchor'],
                core_operations=c,ordinary_comparisons=m,factor_names=packet['unit_factors'],
                certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=counter['*'],additions_subtractions=counter['+']+counter['-'],**degree_bound(packet)))


@lru_cache(None)
def search(normalized, global_unit=True):
    original = base(normalized, global_unit)
    nf = len(original['unit_factors'])
    first = grouped(original,[list(range(nf))],0)
    bound = degree_bound(first)
    weights,r = bound['factor_degree_bounds'],bound['maximum_original_residual_degree_bound']
    plans,statistics = optimizer.optimal_partitions(weights,r)
    records = []
    for plan in plans:
        rec = ledger(grouped(original,plan['partition'],plan['anchor']))
        assert rec['polynomial']['degree_upper_bound'] == plan['degree_upper_bound']
        records.append(rec)
    floor,maskbest = 2*max([r]+weights),None
    for mask in range(1,1 << nf):
        anchor = sum(w for i,w in enumerate(weights) if mask >> i & 1)
        rest = max([r]+[w for i,w in enumerate(weights) if not(mask >> i & 1)])
        if anchor+2*rest < floor: floor,maskbest = anchor+2*rest,mask
    assert min(rec['polynomial']['degree_upper_bound'] for rec in records) == floor
    return dict(normalized=normalized,global_unit=global_unit,statistics=statistics,best_by_group_count=records,
                floor_certificate=dict(lower_bound=floor,anchor_mask=maskbest,
                    anchor_masks_checked=(1 << nf)-1,
                    attained_operations=min(rec['polynomial']['operations'] for rec in records if rec['polynomial']['degree_upper_bound']==floor)))


def frontier(normalized=None, global_unit=None):
    assert normalized is None or type(normalized) is bool
    assert global_unit is None or type(global_unit) is bool
    choices = [rec for n in ((False,True) if normalized is None else (normalized,))
               for g in ((False,True) if global_unit is None else (global_unit,))
               for rec in search(n,g)['best_by_group_count']]
    answer,bound = [],float('inf')
    for rec in sorted(choices,key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'])):
        if rec['polynomial']['degree_upper_bound'] < bound:
            answer.append(rec)
            bound = rec['polynomial']['degree_upper_bound']
    return answer


def build(operations=392,*,normalized=None,global_unit=None):
    rec = next(r for r in frontier(normalized,global_unit) if r['polynomial']['operations']==operations)
    return grouped(base(rec['normalized'],rec['global_unit']),rec['partition'],rec['anchor'])


def grouping_audit(packet,cases=16,seed=385392):
    rows,out = polynomial_source(packet)
    rng,counts = random.Random(seed),Counter()
    for case in range(cases):
        signed = case >= cases//2
        draw = lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
        v = {n:draw() for n in packet['parameters']+packet['auxiliaries']}
        if case%8 == 0: v.update({f'Shat{i}':1 for i in range(24)})
        before = execute(packet['factor_source'],v)
        env = execute(rows,v)
        assert all(env[n] == before[n] for n,_,_,_ in packet['factor_source'])
        at = lambda n:before[n] if isinstance(n,str) else n
        groups = [prod(before[packet['unit_factors'][i]] for i in block) for block in packet['factor_partition']]
        assert groups == [env[n] for n in packet['group_products']]
        anchor = packet['partition_anchor']
        residual = sum((at(a)-at(b))**2 for a,b in packet['ordinary_comparisons'])+sum((g-1)**2 for i,g in enumerate(groups) if i != anchor)
        assert env[out] == (residual if anchor is None else groups[anchor]*(1+residual)-1)
        counts['complete_core_group_and_manual_outputs'] += 1
        counts['signed_outputs'] += signed
    return dict(counts)


def base_maps(global_unit):
    normalized,ordinary = base(True,global_unit),base(False,global_unit)
    rng,counts = random.Random(38552),Counter()
    changed = {'and__ic2','and__ic22',STRONG,'and__R16','and__L17','and__P17'}
    for case in range(80):
        signed = case >= 40
        draw = lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
        v = {n:draw() for n in normalized['parameters']+normalized['auxiliaries']}
        new = execute(normalized['source'],v)
        image = dict(v,**{'and__i':new['and__A']*v['and__i']})
        old = execute(ordinary['source'],image)
        D,N = new['and__A'],new[STRONG]
        assert old['and__ic22']-old['and__R16'] == D*(1-N)
        assert old['and__P17'] == new['and__P17']+D*(N-1)*new['and__aux_square_gap']
        assert all(old[n] == new[n] for n,_,_,_ in ordinary['source'] if n not in changed)
        if not signed: assert min(image.values()) > 0
        counts['ordinary_strong_retained_register_corrections'] += 1
        counts['signed_strong_maps'] += signed
    p = grouped(normalized,[list(range(len(normalized['unit_factors'])))],0)
    rows,out = polynomial_source(p)
    selected = parent if global_unit else parent.parent
    old = selected.build();past,target = selected.polynomial_source(old)
    for case in range(80):
        v = {n:rng.randrange(-3,4) for n in p['parameters']+p['auxiliaries']}
        assert execute(rows,v)[out] == execute(past,v)[target]
        counts['complete_selected_parent_polynomial_identities'] += 1
    return dict(counts)


def global_maps():
    rng,counts = random.Random(385386392),Counter()
    for normalized in (False,True):
        new,old = base(normalized,True),base(normalized,False)
        for case in range(80):
            signed = case >= 40
            draw = lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
            v = {n:draw() for n in new['parameters']+new['auxiliaries']}
            current = execute(new['source'],v)
            past = execute(old['source'],parent.parent_values(v))
            assert all(current[n] == past[n] for n,_,_,_ in old['source'] if n != 'global_lhs__40')
            assert past['global_lhs__40'] == current['global_lhs__40']+1
            assert current[G] == past['P__30']-past['global_lhs__40']+1
            counts['complete_global_slack_core_maps'] += 1
            counts['signed_global_maps'] += signed
    return dict(counts)


def pretyping_audit():
    counts = Counter()
    for normalized in (False,True):
        p = base(normalized)
        for D in (1,2,5):
            for J in (1,3,11):
                for tile in (0,5,14,23):
                    for port in (parent.PORTS[0],parent.PORTS[3],parent.PORTS[-1]):
                        for sign in (-1,1):
                            v = {n:1 for n in p['parameters']+p['auxiliaries']}
                            v['height_slack'] = D;v[f'Shat{tile}'] = J+1
                            B,P = 65536*D,(65536*D-1)*J+1
                            v[port] = P-9-(2 if sign==1 else 0)
                            Sigma = sum(v[n] for n in parent.PORTS)
                            v['global_bound'] = P-Sigma-sign
                            assert min(v.values()) > 0 and Sigma <= P
                            e = execute(p['source'],v)
                            assert e[G] == sign and e['P__30'] == P
                            T = P**34
                            H0,M0,Z = (e[n] for n in ('joined_H__286','joined_M__292','joined_Z__294'))
                            assert all(0 <= v < T for v in (H0,M0,Z))
                            H,M,q = H0+2*T,M0+T,16*B*T
                            F = [q-16*H-12-16*M-10+16*Z+8-1,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
                            assert sum(F) == q-1 and F[0] > 2 and all(0 < v < q for v in F)
                            assert [v%16 for v in F] == [1,4,2,8]
                            r = sum(v*q**i for i,v in enumerate(F))
                            assert r == e['and__bs_packed'] and e['and__wn2'] > r
                            X,Y = e['and__wn2'],e['and__sn2']
                            assert X*Y > 2*r+3 and Y*(r-1) > 2*(2*r+3)
                            counts['both_base_signed_global_pretyping_cases'] += 1
                            counts['height_one_cases'] += D == 1
                            counts['negative_global_unit_cases'] += sign == -1
    return dict(counts)


def guards():
    count = 0
    def reject(call):
        nonlocal count
        try: call()
        except (AssertionError,KeyError): count += 1
        else: raise AssertionError('malformed caller accepted')
    p = base()
    for key,value in [('source',p['source'][:-1]),('auxiliaries',[]),('program_recipe','arbitrary A'),
                      ('letter_codes',{}),('source_verified_contract',{}),('global_unit_register','wrong')]:
        reject(lambda key=key,value=value:grouped(dict(p,**{key:value}),[list(range(13))],0))
    for partition,anchor in [([[0]],0),([[]],None),([list(range(13))],True),
                             ([list(range(13))],1),([list(range(12))+[True]],None),
                             ([list(range(12))+[11]],None)]:
        reject(lambda partition=partition,anchor=anchor:grouped(p,partition,anchor))
    q = build()
    for key,value in [('source',q['source'][:-1]),('comparisons',[]),('unit_register',G),
                      ('identical_fixed_base_positive_zero_set',False)]:
        for api in (polynomial_source,degree_bound):
            reject(lambda api=api,key=key,value=value:api(dict(q,**{key:value})))
    old = parent.build()
    for key,value in [('word_factors',old['word_factors'][:-1]),('ordinary_comparisons',[]),
                      ('source',old['source'][:-1]),('letter_codes',{})]:
        reject(lambda key=key,value=value:source_contract(dict(old,**{key:value})))
    return count


def verify():
    studies = [search(n,g) for n in (False,True) for g in (False,True)]
    records,totals = [],Counter()
    for study in studies:
        for rec in study['best_by_group_count']:
            p = grouped(base(study['normalized'],study['global_unit']),rec['partition'],rec['anchor'])
            result = ledger(p)
            result['audit'] = grouping_audit(p,seed=385500+len(records))
            totals.update(result['audit']);records.append(result)
    fronts = {f'{n},{g}':[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'])
                      for r in frontier(n,g)] for n in (None,False,True) for g in (None,False,True)}
    assert fronts['None,None'] == EXPECTED
    assert fronts['True,True'] == [(385,4714),(387,4707),(389,3608)]
    assert fronts['False,True'] == [(386,4134),(388,2900),(390,2210),(392,1664)]
    assert fronts['True,False'] == [(386,4712),(388,4705),(390,3608)]
    assert fronts['False,False'] == [(387,4132),(389,2900),(391,2210),(393,1664)]
    examples,seen = [],set()
    for n,g in [(n,g) for n in (None,False,True) for g in (None,False,True)]:
        for rec in frontier(n,g):
            key = (rec['normalized'],rec['global_unit'],tuple(map(tuple,rec['partition'])),rec['anchor'])
            if key in seen: continue
            seen.add(key)
            p = grouped(base(key[0],key[1]),rec['partition'],rec['anchor'])
            rows,out = polynomial_source(p)
            result = ledger(p)
            result.update(source=rows,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                          comparisons=p['comparisons'],source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            examples.append(result)
    for normalized,g in [(n,g) for n in (False,True) for g in (False,True)]:
        b = base(normalized,g);nf = len(b['unit_factors'])
        partition = [list(range(i,nf,4)) for i in range(4)]
        for anchor in (None,0,1,2,3):
            totals.update(grouping_audit(grouped(b,partition,anchor),seed=392000+int(normalized)*10+(anchor or 0)))
    return dict(status='PASS_TSEYTIN_GLOBAL_UNIT_FACTOR_PARTITIONS',studies=studies,ledgers=records,
                frontiers=fronts,selected_sources=examples,output_audits=dict(totals),
                strong_base_maps={str(g):base_maps(g) for g in (False,True)},
                global_slack_maps=global_maps(),pretyping=pretyping_audit(),
                source_contracts={str(g):source_contract((parent if g else parent.parent).build(),g) for g in (False,True)},
                independent_small_search=optimizer.small_exhaustive_checks(),rejected_callers=guards(),
                scope='Four fixed bases: normalized/ordinary strong times global unit/retained global equality, unchanged valid recompiled program recipe. Full supplied positive-zero equality within each base on valid slices; global treatment shifts its slack by one and strong treatment may rebuild five auxiliary coordinates. All disjoint factor partitions and SOS/anchor finalizers; exact finite propagated objective, not exact expanded degree or a circuit-wide lower bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args = parser.parse_args()
    result = json.loads(json.dumps(verify()));path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['output_audits'])
