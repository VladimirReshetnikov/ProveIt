"""Typed upper low digit: exact same-coordinate positive zeros,767 ->765.

The old global/bound unit signs may remain negative. Only the new upper
transport sign is forced positive, restoring the complete selected767 source.
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

import gpcp_positive_bound_units767 as parent

PAIR=('hist__U_lhs__314','hist__U_rhs__318')
UPDATE='hist__U_update__313'
TRANSPORT='history_upper_transport_unit'
UNIT='history_upper_transport_product'
REQUIRED={PAIR[0]:('+',UPDATE,1),
 UPDATE:('*','hist__B__3','hist__linear_constant__758'),
 PAIR[1]:('+','hist__H_U','hist__U_terminal__317'),
 'hist__U_terminal__317':('*','hist__P__63','Ufinal'),
 'hist__B__3':('*','hist__height_sum__2',131072),
 'hist__P__63':('+','hist__P_product__62',1),
 'hist__P_product__62':('*','hist__Bm1__61','hist__J__60'),
 'hist__Bm1__61':('-','hist__B__3',1)}
ACTIVE=parent.parent.parent.ACTIVE+('bound_unit_specs',)
execute=parent.execute


def flags(inline_initial,and_bounds,geometry_bounds):
    assert all(type(v)is bool for v in (inline_initial,and_bounds,geometry_bounds))
    return inline_initial,and_bounds,geometry_bounds


def rewrite(old):
    key=flags(*(old.get(k) for k in ('inline_initial','and_bounds','geometry_bounds')))
    assert old==parent.build(inline_initial=key[0],and_bounds=key[1],geometry_bounds=key[2]),'complete canonical767 parent required'
    by={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(by)==len(old['source']) and all(by.get(n)==v for n,v in REQUIRED.items())
    assert old['comparisons'].count(PAIR)==1 and old['comparisons'][-1]==(old['unit_register'],1)
    assert not any(PAIR[0] in (a,b) for n,o,a,b in old['source'])
    exports={k:old[k] for k in ACTIVE if k!='comparisons'}
    assert PAIR[0] not in parent.parent.parent.leaves(exports)
    assert TRANSPORT not in by and UNIT not in by
    source=[row for row in old['source'] if row[0]!=PAIR[0]]
    source.extend([(TRANSPORT,'-',PAIR[1],UPDATE),(UNIT,'*',old['unit_register'],TRANSPORT)])
    pairs=[v for v in old['comparisons'][:-1] if v!=PAIR]+[(UNIT,1)]
    count=Counter(o for n,o,a,b in source);p=deepcopy(old)
    p.update(source=source,comparisons=pairs,unit_factors=old['unit_factors']+[TRANSPORT],unit_register=UNIT,
             operations=len(source),multiplications=count['*'],additions_subtractions=count['+']+count['-'],equations=len(pairs),
             upper_transport_parent=old,upper_transport_unit=True,upper_transport_register=TRANSPORT,
             history_upper_transport=dict(initial=1,radix='hist__B__3',history_scale='hist__P__63',
                                          update=UPDATE,rhs=PAIR[1],unit=TRANSPORT),
             identical_complete_integer_polynomial=False,identical_positive_zero_set=True,
             positive_zero_bijection=True,positive_zero_surjection=True,
             positive_zero_equality_scope='Full same-coordinate positive zeros for all positive program parameters, relative to the selected767 parent.',
             projection='Identity on supplied positive zeros. Typed upper low digit forces the new transport unit+1; existing G/H signs need not be positive.',
             positive_section='Identity on supplied positive zeros of the selected767 parent.')
    assert p['operations']==old['operations']+1 and p['equations']==old['equations']-1
    assert p['history_packet']==old['history_packet']
    return p


@lru_cache(None)
def _build(inline_initial,and_bounds,geometry_bounds):
    return rewrite(parent.build(inline_initial=inline_initial,and_bounds=and_bounds,geometry_bounds=geometry_bounds))


def build(*,inline_initial=True,and_bounds=True,geometry_bounds=True):
    return deepcopy(_build(*flags(inline_initial,and_bounds,geometry_bounds)))


def checked(packet):
    key=flags(*(packet.get(k) for k in ('inline_initial','and_bounds','geometry_bounds')))
    assert packet==_build(*key),'complete canonical upper-transport765 packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.parent.parent.polynomial_source(packet)


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.parent.raw_degrees(packet)


def degree_audit(packet=None):
    if packet is None:packet=build()
    checked(packet);old=packet['upper_transport_parent'];prior=parent.degree_audit(old)
    degree=degree_dictionary(packet);d=lambda n:degree[n] if isinstance(n,str) else 0
    olddegree=parent.degree_dictionary(old)
    assert all(degree[n]==v for n,v in olddegree.items() if n!=PAIR[0])
    increment=68 if packet['inline_initial'] else 3
    assert d(PAIR[1])==d('hist__P__63')+1==increment>d(UPDATE)
    assert d(TRANSPORT)==increment
    assert ('hist__and__R10b','hist__and__R11') in packet['comparisons']
    assert d('hist__and__bs_packed')==prior['maximum_outer_degree']>increment
    assert max(max(d(a),d(b)) for a,b in packet['comparisons'][:-1])==prior['maximum_outer_degree']
    assert d(UNIT)==prior['unit_degree']+increment
    rows,out=polynomial_source(packet)
    for n,o,a,b in rows:
        if n not in degree:degree[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    assert degree[out]==prior['exact_degree']+increment
    return dict(exact_degree=degree[out],parent_exact_degree=prior['exact_degree'],degree_increment=increment,
                unit_degree=d(UNIT),maximum_outer_degree=prior['maximum_outer_degree'],
                transport_degree=increment,transport_strict_leader='leading(P_history)*Ufinal',
                exactness_reason='The upper rhs has strictly greater degree than its update; P=(131072D-1)J+1 has nonzero leader. The old unit and remaining maximal first-index residual have unchanged nonzero leaders.')


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);count=Counter(o for n,o,a,b in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=count['*'],additions_subtractions=count['+']+count['-'],output=out),
                degree=degree_audit(packet))


def source_audit(cases=24):
    rng=random.Random(765767);count=Counter()
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo);old=p['upper_transport_parent']
        rows,out=polynomial_source(p);before,target=parent.polynomial_source(old)
        for i in range(cases):
            signed=i>=cases//2
            values={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in p['parameters']+p['auxiliaries']}
            if i%6==0:values.update({f'hist__Shat{j}':1 for j in range(57)});count['zero_selector_contexts']+=1
            e=execute(rows,values);past=execute(before,values)
            assert all(e[n]==past[n] for n,o,a,b in old['source'] if n!=PAIR[0])
            t=e[TRANSPORT];assert past[PAIR[0]]-past[PAIR[1]]==1-t
            u=prod(e[f] for f in old['unit_factors']);at=lambda n:e[n] if isinstance(n,str) else n
            square=sum((at(a)-at(b))**2 for a,b in p['comparisons'][:-1])
            assert e[out]==u*t*(1+square)-1
            assert e[out]-past[target]==u*(t-1)*(square-t+2)
            count['complete_retained_register_maps']+=1;count['complete_output_corrections']+=1;count['signed_cases']+=signed
    return dict(count)


def leading_audit(packet,prime):
    rows,out=polynomial_source(packet);degree=degree_dictionary(packet)
    for n,o,a,b in rows:
        d=lambda z:degree[z] if isinstance(z,str) else 0
        if n not in degree:degree[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    top={n:(i+2) for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
    for pre in ('geo__','and__','hist__and__'):
        top[pre+'tau_gap']=top[pre+'eta']=top[pre+'zeta']=1
    for n,o,a,b in rows:
        da=degree[a] if isinstance(a,str) else 0;db=degree[b] if isinstance(b,str) else 0
        va=top[a] if isinstance(a,str) else a;vb=top[b] if isinstance(b,str) else b
        top[n]=(va*vb if o=='*' else (va if da==degree[n] else 0)+(1 if o=='+' else -1)*(vb if db==degree[n] else 0))%prime
        for pre in ('geo__','and__','hist__and__'):
            if n==pre+'R15':
                assert degree[n]==degree[pre+'cam2']+degree[pre+'gam']
                top[n]=2*top[pre+'cam2']*top[pre+'gam']%prime
    assert all(top[f] for f in packet['unit_factors']) and top[out]
    assert top[TRANSPORT]==top['hist__P__63']*top['Ufinal']%prime
    return dict(prime=prime,degree=degree[out],output_leader_value=top[out],transport_leader_value=top[TRANSPORT])


def typed_audit():
    count=Counter()
    for D in (1,2,3,4,7,16):
        B=131072*D
        for duration in (1,2,3):
            P=B**duration
            for digits in product(range(min(D,5)),repeat=duration):
                HU=sum(v*B**i for i,v in enumerate(digits))
                for final in (1,D,D+2):
                    for sign in (-1,1):
                        remainder=(HU+P*final-sign)%B
                        if remainder==0:
                            assert sign==1 and digits[0]==1
                            update=(HU+P*final-sign)//B
                            assert HU+P*final-B*update==1
                            count['positive_upper_boundary_solutions']+=1
                        count['typed_low_digit_sign_checks']+=1
    # Literal physical maps, own affine recurrence and base-B packing.
    maps=build()['history_packet']['maps'];assert len(maps)==57
    rng=random.Random(76557)
    for case in range(48):
        selection=[rng.randrange(57) for _ in range(1+case%8)];states=[1]
        for tile in selection:
            a,c,b,d=maps[tile];assert a>0 and c>=0 and a+c<131072
            states.append(a*states[-1]+c)
        D=1
        while D<=max(states):D*=2
        B=131072*D;P=B**len(selection)
        HU=sum(v*B**i for i,v in enumerate(states[:-1]));NU=sum(v*B**i for i,v in enumerate(states[1:]))
        assert HU+P*states[-1]-B*NU==1
        count['literal57_tile_upper_paths']+=1;count['literal_tile_rows']+=len(selection)
    # Old flexible signs need not be positive; only T is fixed.
    for n in (1,3,5):
        for signs in product((-1,1),repeat=n):
            if prod(signs)==1:assert prod((*signs,1))==1;count['old_signed_product_patterns_retained']+=1
    return dict(count,scope='Typed scalar and literal upper-history components; no complete compiled Pell tuples.')


def guards():
    count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    old=parent.build()
    for key,value in [('source',old['source'][:-1]),('comparisons',[]),('history_packet',{}),('parameters',[]),('unit_factors',[]),('projection','bad')]:
        reject(lambda key=key,value=value:rewrite(dict(old,**{key:value})))
    for n in REQUIRED:
        rows=[(k,o,a,17 if k==n else b) for k,o,a,b in old['source']]
        reject(lambda rows=rows:rewrite(dict(old,source=rows)))
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo)
        for key,value in [('source',p['source'][:-1]),('comparisons',[]),('positive_zero_equality_scope','only inputs'),('history_upper_transport',{}),('unit_register','bad')]:
            for api in (polynomial_source,degree_audit):
                reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
    for key in ('inline_initial','and_bounds','geometry_bounds'):reject(lambda key=key:build(**{key:1}))
    return count


def verify():
    forms=[]
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo);old=p['upper_transport_parent']
        rows,out=polynomial_source(p);record=ledger(p);prior=parent.ledger(old)
        assert record['polynomial']['operations']==prior['polynomial']['operations']-2
        assert record['polynomial']['multiplications']==prior['polynomial']['multiplications']
        assert record['polynomial']['additions_subtractions']==prior['polynomial']['additions_subtractions']-2
        assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries']
        by={n:(a,b) for n,o,a,b in rows};seen=set();todo=[out]
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in by and n not in seen:seen.add(n);todo.extend(by[n])
        assert seen==by.keys()
        record.update(inline_initial=inline,and_bounds=ands,geometry_bounds=geo,source=rows,output=out,
                      parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                      leading_certificates=[leading_audit(p,v) for v in (1000000007,1000000009)],
                      source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        forms.append(record)
    return dict(status='PASS_GPCP_UPPER_TRANSPORT_UNIT765',forms=forms,source_audit=source_audit(),
                typed_audit=typed_audit(),rejected_callers=guards(),
                scope='Full same-coordinate positive-zero equality with selected767 parent for all positive program parameters. Old G/H signs may remain negative; no off-zero polynomial identity or complete Pell fixtures.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print({k:v for k,v in result.items() if k not in ('status','forms')})
