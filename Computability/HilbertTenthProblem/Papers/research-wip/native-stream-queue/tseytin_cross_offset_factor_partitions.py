"""Transport the full four-base factor family through an exact 2M rewrite.

Every matching old/new plan is the same integer polynomial on identical
coordinates. The finite factor objective and all degree bounds are
unchanged; every complete source costs two fewer multiplications.
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

import tseytin_cross_offsets383 as local
import tseytin_global_unit_factor_partitions as previous

scale,execute,closure = local.scale,local.execute,previous.closure
EXPECTED = [(383,4714),(384,4134),(385,4132),(386,2900),(388,2210),(390,1664)]


def _exports(packet):
    # Export the entire active non-source metadata, not just the two known
    # affine ports. Historical source bodies are not active value exports.
    return {k:v for k,v in packet.items() if k not in ('source','factor_source')}


def rewrite_base(old):
    assert old == previous.base(old['word_strong_normalized'],old['global_unit']), 'complete canonical prior factor base required'
    rows = local.rewrite_rows(old['source'],exported=_exports(old))
    rows = scale.sort_source(rows,old['parameters']+old['auxiliaries'])
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    assert len(rows) == len(old['source'])-2
    assert not set(local.PRIVATE)&local.leaves(_exports(old))
    return dict(deepcopy(old),source=rows,factor_source=rows,cross_offset_factor_base=True,
                identity_reference='matching canonical prior global-unit/equality strong factor base',
                projection='Both affine boundary ports, every factor and comparison agree over all integers with the matching prior base; supplied coordinates and valid program recipes are unchanged.')


@lru_cache(None)
def _base(normalized,global_unit):
    return rewrite_base(previous.base(normalized,global_unit))


def base(normalized=True,global_unit=True):
    assert type(normalized) is bool and type(global_unit) is bool
    return deepcopy(_base(normalized,global_unit))


def rewrite(old):
    """Rewrite a fully guarded prior base/partition/anchor packet."""
    previous.checked_packet(old)
    normalized,global_unit = old['word_strong_normalized'],old['global_unit']
    newbase = base(normalized,global_unit)
    rows = local.rewrite_rows(old['source'],exported=_exports(old))
    rows = scale.sort_source(rows,old['parameters']+old['auxiliaries'])
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    result = scale.metadata(dict(deepcopy(old),source=rows,
        factor_source=newbase['factor_source'],cross_offset_factor_base=True,
        cross_offset_factor_partition=True,
        identity_map_to_matching_prior_plan=True,
        identity_reference='matching canonical global-unit factor partition with the same two base choices, partition and anchor',
        projection='Exact whole integer-polynomial identity with the matching prior plan, on the identical coordinates and program numerals. Original within-base and cross-base semantic scopes are retained.'))
    assert result['operations'] == old['operations']-2
    assert result['multiplications'] == old['multiplications']-2
    assert result['additions_subtractions'] == old['additions_subtractions']
    for key in ('parameters','auxiliaries','unit_factors','ordinary_comparisons','comparisons',
                'interfaces','program_recipe','letter_codes','tiles','unit_register',
                'group_products','factor_partition','partition_anchor','source_verified_contract'):
        assert result[key] == old[key],key
    return result


def grouped(original,partition,anchor):
    assert original == base(original['word_strong_normalized'],original['global_unit']), 'complete canonical cross-offset factor base required'
    oldbase = previous.base(original['word_strong_normalized'],original['global_unit'])
    old = previous.grouped(oldbase,partition,anchor)
    return rewrite(old)


def checked_packet(packet):
    assert packet == grouped(base(packet['word_strong_normalized'],packet['global_unit']),
                             packet['factor_partition'],packet['partition_anchor']), 'complete canonical successor plan required'


def polynomial_source(packet):
    checked_packet(packet)
    return previous.word.norms.polynomial_source(packet,sum_of_squares=packet['partition_anchor'] is None)


def degree_dictionary(packet):
    """Low-level guarded norm propagation; public ledgers check the packet."""
    return previous.degree_dictionary(packet)


def degree_bound(packet):
    checked_packet(packet)
    degrees = degree_dictionary(packet)
    d = lambda n:degrees[n] if isinstance(n,str) else 0
    weights = [d(n) for n in packet['unit_factors']]
    residual = max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons'])
    groups = [sum(weights[i] for i in g) for g in packet['factor_partition']]
    assert groups == [d(n) for n in packet['group_products']]
    anchor = packet['partition_anchor']
    bound = 2*max([residual]+groups) if anchor is None else groups[anchor]+2*max([residual]+[v for j,v in enumerate(groups) if j != anchor])
    return dict(degree_upper_bound=bound,factor_degree_bounds=weights,
                maximum_original_residual_degree_bound=residual,
                group_degree_bounds=groups,exact_degree_claimed=False)


def ledger(packet):
    rows,out = polynomial_source(packet)
    count = Counter(o for _,o,_,_ in rows)
    c,n,m,g = len(packet['factor_source']),len(packet['unit_factors']),len(packet['ordinary_comparisons']),len(packet['factor_partition'])
    assert len(rows) == c+n+3*m-1+2*g
    assert len(closure(rows,[out])) == len(rows)
    return dict(normalized=packet['word_strong_normalized'],global_unit=packet['global_unit'],
                partition=packet['factor_partition'],anchor=packet['partition_anchor'],
                core_operations=c,ordinary_comparisons=m,factor_names=packet['unit_factors'],
                certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=count['*'],
                                additions_subtractions=count['+']+count['-'],**degree_bound(packet)))


@lru_cache(None)
def search(normalized,global_unit=True):
    old = previous.search(normalized,global_unit)
    records = []
    for rec in old['best_by_group_count']:
        new = ledger(grouped(base(normalized,global_unit),rec['partition'],rec['anchor']))
        for form in ('certificate','polynomial'):
            assert new[form]['operations'] == rec[form]['operations']-2
            assert new[form]['multiplications'] == rec[form]['multiplications']-2
            assert new[form]['additions_subtractions'] == rec[form]['additions_subtractions']
        assert new['polynomial']['degree_upper_bound'] == rec['polynomial']['degree_upper_bound']
        records.append(new)
    floor = dict(old['floor_certificate'],attained_operations=old['floor_certificate']['attained_operations']-2)
    assert min(r['polynomial']['degree_upper_bound'] for r in records) == floor['lower_bound']
    return dict(normalized=normalized,global_unit=global_unit,
                statistics=old['statistics'],best_by_group_count=records,
                floor_certificate=floor,
                objective_transport='Every partition/anchor keeps its bound and costs exactly2M less; reuse the proved complete prior subset search.')


def frontier(normalized=None,global_unit=None):
    assert normalized is None or type(normalized) is bool
    assert global_unit is None or type(global_unit) is bool
    choices = [r for n in ((False,True) if normalized is None else (normalized,))
               for g in ((False,True) if global_unit is None else (global_unit,))
               for r in search(n,g)['best_by_group_count']]
    result,best = [],float('inf')
    for r in sorted(choices,key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'])):
        if r['polynomial']['degree_upper_bound'] < best:
            result.append(r);best = r['polynomial']['degree_upper_bound']
    return result


def build(operations=390,*,normalized=None,global_unit=None):
    rec = next(r for r in frontier(normalized,global_unit) if r['polynomial']['operations']==operations)
    return grouped(base(rec['normalized'],rec['global_unit']),rec['partition'],rec['anchor'])


def plan_audit(packet,cases=8,seed=383390):
    old = previous.grouped(previous.base(packet['word_strong_normalized'],packet['global_unit']),
                           packet['factor_partition'],packet['partition_anchor'])
    rows,out = polynomial_source(packet);before,target = previous.polynomial_source(old)
    newdegree = degree_dictionary(dict(packet,source=rows))
    olddegree = previous.degree_dictionary(dict(old,source=before))
    assert set(newdegree) == set(olddegree)-set(local.DELETED)
    assert all(newdegree[n] == olddegree[n] for n in newdegree)
    assert newdegree[out] == degree_bound(packet)['degree_upper_bound']
    assert len(closure(rows,[out])) == len(rows)
    counts,rng = Counter(),random.Random(seed)
    counts['complete_degree_dictionary_opcode_closure_checks'] += 1
    for case in range(cases):
        signed = case >= cases//2
        draw = lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
        values = {n:draw() for n in packet['parameters']+packet['auxiliaries']}
        if case%4 == 0:
            values.update({f'Shat{i}':1 for i in range(24)})
            counts['zero_selector_cases'] += 1
        new,past = execute(rows,values),execute(before,values)
        restored = local.restore_private(new,old)
        assert all(restored[n] == past[n] for n,_,_,_ in before)
        assert new[out] == past[target]
        assert all(new[n] == past[n] for n in local.BOUNDARY+packet['unit_factors']+packet['group_products'])
        at = lambda n:new[n] if isinstance(n,str) else n
        groups = [prod(new[packet['unit_factors'][i]] for i in block) for block in packet['factor_partition']]
        anchor = packet['partition_anchor']
        residual = sum((at(a)-at(b))**2 for a,b in packet['ordinary_comparisons'])+sum((v-1)**2 for i,v in enumerate(groups) if i != anchor)
        assert new[out] == (residual if anchor is None else groups[anchor]*(1+residual)-1)
        counts['complete_private_restore_factor_parent_manual_outputs'] += 1
        counts['signed_outputs'] += signed
    return dict(counts)


def direct_parent_audit():
    counts,rng = Counter(),random.Random(383384)
    for global_unit in (False,True):
        b = base(True,global_unit)
        p = grouped(b,[list(range(len(b['unit_factors'])))],0)
        rows,out = polynomial_source(p)
        direct = local.build(global_unit=global_unit)
        other,target = local.polynomial_source(direct)
        for case in range(32):
            values = {n:rng.randrange(-3,4) for n in p['parameters']+p['auxiliaries']}
            assert execute(rows,values)[out] == execute(other,values)[target]
            counts['complete383_or384_reassociation_identities'] += 1
    return dict(counts)


def guards():
    count = 0
    def reject(call):
        nonlocal count
        try: call()
        except (AssertionError,KeyError): count += 1
        else: raise AssertionError('malformed caller accepted')
    old = previous.base()
    for key,val in [('source',old['source'][:-1]),('interfaces',{}),('auxiliaries',[]),
                    ('program_recipe','arbitrary'),('source_verified_contract',{}),
                    ('extra_active_export',{'nested':[local.PRIVATE[0]]})]:
        reject(lambda key=key,val=val:rewrite_base(dict(old,**{key:val})))
    oldplan = previous.build()
    for key,val in [('source',oldplan['source'][:-1]),('comparisons',[]),('unit_register',local.PRIVATE[1])]:
        reject(lambda key=key,val=val:rewrite(dict(oldplan,**{key:val})))
    b = base()
    for partition,anchor in [([[0]],0),([[]],None),([list(range(13))],True),
                             ([list(range(12))+[True]],None),([list(range(13))],1)]:
        reject(lambda partition=partition,anchor=anchor:grouped(b,partition,anchor))
    p = build()
    for key,val in [('source',p['source'][:-1]),('identity_map_to_matching_prior_plan',False),
                    ('factor_source',p['factor_source'][:-1]),('program_recipe','wrong')]:
        for api in (polynomial_source,degree_bound):
            reject(lambda key=key,val=val,api=api:api(dict(p,**{key:val})))
    for n,g in [(1,True),(True,1),(False,None)]:
        reject(lambda n=n,g=g:base(n,g))
    return count


def verify():
    studies = [search(n,g) for n in (False,True) for g in (False,True)]
    totals,records = Counter(),[]
    for study in studies:
        for rec in study['best_by_group_count']:
            p = grouped(base(study['normalized'],study['global_unit']),rec['partition'],rec['anchor'])
            result = ledger(p)
            result['audit'] = plan_audit(p,seed=383000+len(records))
            totals.update(result['audit']);records.append(result)
    fronts = {f'{n},{g}':[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'])
                         for r in frontier(n,g)] for n in (None,False,True) for g in (None,False,True)}
    assert fronts['None,None'] == EXPECTED
    for n in (None,False,True):
        for g in (None,False,True):
            assert fronts[f'{n},{g}'] == [(r['polynomial']['operations']-2,r['polynomial']['degree_upper_bound'])
                                         for r in previous.frontier(n,g)]
    examples,seen = [],set()
    for n in (None,False,True):
        for g in (None,False,True):
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
    for n in (False,True):
        for g in (False,True):
            b = base(n,g);nf = len(b['unit_factors'])
            partition = [list(range(i,nf,4)) for i in range(4)]
            for anchor in (None,0,1,2,3):
                totals.update(plan_audit(grouped(b,partition,anchor),seed=390000+int(n)*10+int(g)*20+(anchor or 0)))
    return dict(status='PASS_TSEYTIN_CROSS_OFFSET_FACTOR_PARTITIONS',studies=studies,
                ledgers=records,frontiers=fronts,selected_sources=examples,
                output_audits=dict(totals),direct_parent=direct_parent_audit(),
                rejected_callers=guards(),
                scope='Exact whole integer-polynomial identity to every matching prior four-base partition/anchor plan; two fewer multiplications, all supplied coordinates/program numerals and propagated degrees unchanged. Full within-base positive-zero and cross-base semantics are exactly those of the frozen parent; finite objective only.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args = parser.parse_args()
    result = json.loads(json.dumps(verify()));path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['output_audits'])
