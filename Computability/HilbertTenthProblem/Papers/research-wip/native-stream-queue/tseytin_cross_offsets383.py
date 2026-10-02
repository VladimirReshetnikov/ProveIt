"""Reuse opposite-coordinate selector sums:385 ->383 exactly.

Two multiplications disappear from all four global/equality and power
interfaces. Supplied coordinates, complete polynomials and degrees agree.
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

scale=parent.scale
execute=parent.execute
REQUIRED={'group_sum__221': ('+', 'Shat14', 'Shat16'),
 'group_sum__222': ('+', 'Shat21', 'group_sum__221'),
 'group_sum__223': ('+', 'Shat23', 'group_sum__222'),
 'group_sum__228': ('+', 'Shat15', 'Shat17'),
 'group_sum__229': ('+', 'Shat20', 'group_sum__228'),
 'group_sum__230': ('+', 'Shat22', 'group_sum__229'),
 'linear_group__370': ('+', 'Shat14', 'Shat15'),
 'linear_coefficient__371': ('*', 'linear_group__370', 12),
 'linear_group__372': ('+', 'Shat16', 'Shat17'),
 'linear_coefficient__373': ('*', 'linear_group__372', 20),
 'linear_coefficient__398': ('*', 255, 'group_sum__221'),
 'linear_coefficient__400': ('*', 'Shat20', 512),
 'linear_coefficient__401': ('*', 'Shat22', 1024),
 'linear_coefficient__417': ('*', 255, 'group_sum__228'),
 'linear_coefficient__419': ('*', 'Shat21', 512),
 'linear_coefficient__420': ('*', 'Shat23', 1024),
 'linear_coefficient__397': ('-', 'linear_coefficient__398', 'permuted_delta_U'),
 'linear_sum__405': ('+', 'linear_coefficient__397', 'linear_sum__403'),
 'linear_sum__407': ('+', 'linear_coefficient__399', 'linear_sum__405'),
 'linear_sum__408': ('+', 'linear_coefficient__400', 'linear_sum__407'),
 'linear_sum__409': ('+', 'linear_coefficient__401', 'linear_sum__408'),
 'linear_coefficient__416': ('-', 'linear_coefficient__417', 'permuted_delta_V'),
 'linear_sum__424': ('+', 'linear_coefficient__416', 'linear_sum__422'),
 'linear_sum__426': ('+', 'linear_coefficient__418', 'linear_sum__424'),
 'linear_sum__427': ('+', 'linear_coefficient__419', 'linear_sum__426'),
 'linear_sum__428': ('+', 'linear_coefficient__420', 'linear_sum__427'),
 'linear_sum__389': ('+', 'linear_coefficient__371', 'linear_sum__388'),
 'linear_sum__390': ('+', 'linear_coefficient__373', 'linear_sum__389'),
 'linear_sum__391': ('+', 'linear_coefficient__375', 'linear_sum__390'),
 'c2_shared_update_offset': ('-', 'linear_sum__391', 45194),
 'linear_constant__411': ('+', 'c2_shared_update_offset', 'linear_sum__409'),
 'linear_constant__430': ('+', 'c2_shared_update_offset', 'linear_sum__428')}
CHANGES={'linear_coefficient__371': ('*', 'linear_group__370', 267),
 'linear_coefficient__373': ('*', 'linear_group__372', 275),
 'linear_coefficient__398': ('*', -767, 'group_sum__228'),
 'linear_coefficient__417': ('*', -767, 'group_sum__221'),
 'linear_coefficient__400': ('+', 'group_sum__230', 'Shat22'),
 'linear_coefficient__419': ('+', 'group_sum__223', 'Shat23'),
 'linear_coefficient__401': ('*', 512, 'linear_coefficient__400'),
 'linear_coefficient__420': ('*', 512, 'linear_coefficient__419'),
 'linear_sum__409': ('+', 'linear_coefficient__401', 'linear_sum__407'),
 'linear_sum__428': ('+', 'linear_coefficient__420', 'linear_sum__426')}
DELETED=['linear_sum__408', 'linear_sum__427']
PRIVATE=['c2_shared_update_offset',
 'linear_coefficient__371',
 'linear_coefficient__373',
 'linear_coefficient__397',
 'linear_coefficient__398',
 'linear_coefficient__400',
 'linear_coefficient__401',
 'linear_coefficient__416',
 'linear_coefficient__417',
 'linear_coefficient__419',
 'linear_coefficient__420',
 'linear_sum__389',
 'linear_sum__390',
 'linear_sum__391',
 'linear_sum__405',
 'linear_sum__407',
 'linear_sum__408',
 'linear_sum__409',
 'linear_sum__424',
 'linear_sum__426',
 'linear_sum__427',
 'linear_sum__428']
BOUNDARY=['linear_constant__411', 'linear_constant__430']
CONSUMERS={'c2_shared_update_offset': ['linear_constant__411', 'linear_constant__430'],
 'linear_coefficient__371': ['linear_sum__389'],
 'linear_coefficient__373': ['linear_sum__390'],
 'linear_coefficient__397': ['linear_sum__405'],
 'linear_coefficient__398': ['linear_coefficient__397'],
 'linear_coefficient__400': ['linear_sum__408'],
 'linear_coefficient__401': ['linear_sum__409'],
 'linear_coefficient__416': ['linear_sum__424'],
 'linear_coefficient__417': ['linear_coefficient__416'],
 'linear_coefficient__419': ['linear_sum__427'],
 'linear_coefficient__420': ['linear_sum__428'],
 'linear_sum__389': ['linear_sum__390'],
 'linear_sum__390': ['linear_sum__391'],
 'linear_sum__391': ['c2_shared_update_offset'],
 'linear_sum__405': ['linear_sum__407'],
 'linear_sum__407': ['linear_sum__408'],
 'linear_sum__408': ['linear_sum__409'],
 'linear_sum__409': ['linear_constant__411'],
 'linear_sum__424': ['linear_sum__426'],
 'linear_sum__426': ['linear_sum__427'],
 'linear_sum__427': ['linear_sum__428'],
 'linear_sum__428': ['linear_constant__430']}


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):return set().union(*(leaves(k)|leaves(v) for k,v in value.items()),set())
    if isinstance(value,(tuple,list)):return set().union(*(leaves(v) for v in value),set())
    return set()


def rewrite_rows(rows,*,exported=()):
    """Local guarded identity; host canonical contract and sort remain required."""
    actual={n:(o,a,b) for n,o,a,b in rows}
    assert len(actual)==len(rows),'unique source definitions required'
    assert all(actual.get(n)==v for n,v in REQUIRED.items()),'exact C2 offset and paid group definitions required'
    for name,want in CONSUMERS.items():
        assert sorted(n for n,_,a,b in rows if name in (a,b))==want,'changed private offset gained a consumer'
    assert not set(PRIVATE)&leaves(exported),'changed private offset exported'
    return [(n,*CHANGES.get(n,(o,a,b))) for n,o,a,b in rows if n not in DELETED]


def selected_parent(global_unit):
    assert type(global_unit)is bool
    return parent if global_unit else parent.parent


def rewrite(old,*,global_unit=True):
    api=selected_parent(global_unit);merge=old.get('merge_units')
    assert type(merge)is bool and old==api.build(merge_units=merge),'complete canonical385/386 parent required'
    active=('parameters','auxiliaries','comparisons','ordinary_comparisons','interfaces',
            'unit_register','word_unit_register','power_unit_register','word_factors','power_factors')
    rows=rewrite_rows(old['source'],exported={k:old[k] for k in active})
    rows=scale.sort_source(rows,old['parameters']+old['auxiliaries'])
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=rows,cross_offsets=True,cross_offsets_parent=old,
        cross_offsets_global_unit=global_unit,identical_complete_polynomial=True,
        identical_positive_zero_set=True,positive_zero_bijection=True,
        positive_zero_bijection_scope='identity on all supplied positive coordinates, before valid-program restriction',
        identity_reference='canonical global-unit385' if global_unit else 'canonical shared-offset386',
        projection='Exact integer-polynomial identity on the same supplied coordinates and program recipe with the selected385/386 parent.'))
    assert p['operations']==old['operations']-2 and p['multiplications']==old['multiplications']-2
    assert p['additions_subtractions']==old['additions_subtractions']
    return p


@lru_cache(None)
def build(*,global_unit=True,merge_units=True):
    return rewrite(selected_parent(global_unit).build(merge_units=merge_units),global_unit=global_unit)


def checked_packet(packet):
    assert packet==build(global_unit=packet['cross_offsets_global_unit'],merge_units=packet['merge_units']),'complete canonical cross-offset packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.parent.parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.parent.parent.parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet);d=lambda v:degrees[v] if isinstance(v,str) else 0
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def restore_private(env,old):
    return execute([row for row in old['source'] if row[0] in PRIVATE],env)


def exact_identity_audit():
    import sympy as sp
    names=set(REQUIRED)
    external=sorted({v for op,a,b in REQUIRED.values() for v in (a,b) if isinstance(v,str) and v not in names})
    values={n:sp.Symbol(n) for n in external}
    old=scale.sort_source([(n,*v) for n,v in REQUIRED.items()],external)
    # The local fixture has exactly the declared private consumers.
    new=scale.sort_source(rewrite_rows(old,exported=BOUNDARY),external)
    before,after=execute(old,values),execute(new,values)
    for name in BOUNDARY:assert sp.expand(after[name]-before[name])==0
    h14,h15,h16,h17=(values[f'Shat{i}'] for i in range(14,18))
    shift=255*(h14+h15+h16+h17)
    assert sp.expand(after['c2_shared_update_offset']-before['c2_shared_update_offset']-shift)==0
    for name in ('linear_sum__409','linear_sum__428'):
        assert sp.expand(after[name]-before[name]+shift)==0
    return dict(exact_boundary_identities=2,exact_private_shift_identities=3,
                independent_external_symbols=len(external),scope='All integers; no positive, one-hot, height, native or program hypothesis.')


def source_audit(cases=64):
    rng=random.Random(383385);counts=Counter()
    for global_unit in (False,True):
      api=selected_parent(global_unit)
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge);old=p['cross_offsets_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%16==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_decoded_selector_cases']+=1
            e=execute(p['source'],values);past=execute(old['source'],values)
            restored=restore_private(e,old)
            assert all(restored[n]==past[n] for n,_,_,_ in old['source'])
            assert all(e[n]==past[n] for n in BOUNDARY)
            counts['complete_private_restore_register_maps']+=1;counts['signed_register_maps']+=signed
            for sos in (False,True):
                rows,out=polynomial_source(p,sum_of_squares=sos);other,target=api.polynomial_source(old,sum_of_squares=sos)
                env=execute(rows,values);assert env[out]==execute(other,values)[target]
                at=lambda v:env[v] if isinstance(v,str) else v
                S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
                W=prod(env[n] for n in p['word_factors']);E=prod(env[n] for n in p['power_factors'])
                manual=(W*E-1)**2+S if merge and sos else W*E*(1+S)-1 if merge else (W-1)**2+(E-1)**2+S if sos else W*(1+S+(E-1)**2)-1
                assert env[out]==manual
                counts['complete_parent_and_manual_outputs']+=1;counts['signed_outputs']+=signed
    return dict(counts)


def guards():
    old=parent.build();count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for name in REQUIRED:
        bad=[(n,o,a,17 if n==name else b) for n,o,a,b in old['source']]
        reject(lambda bad=bad:rewrite_rows(bad))
    for name in PRIVATE:
        reject(lambda name=name:rewrite_rows(old['source']+[('extra_consumer','+',name,1)]))
        reject(lambda name=name:rewrite_rows(old['source'],exported={'nested':[{'port':(name,)}]}))
    reject(lambda:rewrite_rows(old['source']+[old['source'][0]]))
    for key,val in [('interfaces',{}),('auxiliaries',[]),('program_recipe','new'),('word_factors',[])]:
        reject(lambda key=key,val=val:rewrite(dict(old,**{key:val})))
    p=build()
    for key,val in [('source',p['source'][:-1]),('identity_reference','unrelated'),('comparisons',[])]:
        for api in (polynomial_source,degree_bound):reject(lambda key=key,val=val,api=api:api(dict(p,**{key:val})))
    return count


def verify():
    forms=[]
    for global_unit in (False,True):
      api=selected_parent(global_unit)
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge);old=p['cross_offsets_parent']
        before=api.degree_dictionary(old);after=degree_dictionary(p)
        assert set(after)==set(before)-set(DELETED) and all(after[n]==before[n] for n in after)
        for sos in (False,True):
            rows,out=polynomial_source(p,sum_of_squares=sos);record=ledger(p,sum_of_squares=sos)
            lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=[out]
            while todo:
                n=todo.pop()
                if isinstance(n,str) and n in lookup and n not in seen:seen.add(n);todo.extend(lookup[n])
            assert seen==lookup.keys()
            assert record['polynomial']['operations']==(383 if global_unit else 384)+(0 if merge else 2)
            assert record['polynomial']['multiplications']==176
            assert degree_bound(p,sum_of_squares=sos)==api.degree_bound(old,sum_of_squares=sos)
            record.update(global_unit=global_unit,merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_CROSS_OFFSETS383',forms=forms,exact=exact_identity_audit(),
        source_audit=source_audit(),rejected_callers=guards(),
        scope='Exact complete integer-polynomial identity with selected385/386 parents on identical supplied coordinates and program recipes, including all positive domains.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit'])
