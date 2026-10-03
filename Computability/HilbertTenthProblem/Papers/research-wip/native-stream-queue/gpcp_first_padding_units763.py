"""Two independently forced first-padding units: complete U15,2 765 -> 763.

The complete supplied positive zero sets agree for every positive program
parameter. Existing global/bound signs remain unrestricted. This is not
an off-zero polynomial identity or a second-padding-unit claim.
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

import gpcp_upper_transport_unit765 as parent

PREFIXES=('and__','hist__and__')
FACTORS=tuple(pre+'first_padding_unit' for pre in PREFIXES)
PRODUCTS=tuple(pre+'first_padding_product' for pre in PREFIXES)
PAIRS=tuple((pre+'input_A',pre+'padded_A') for pre in PREFIXES)
CHANGED=tuple(pre+'padded_A' for pre in PREFIXES)
ACTIVE=parent.ACTIVE+('history_upper_transport',)
execute=parent.execute
flags=parent.flags


def rewrite(old):
    key=flags(*(old.get(k) for k in ('inline_initial','and_bounds','geometry_bounds')))
    assert old==parent.build(inline_initial=key[0],and_bounds=key[1],geometry_bounds=key[2]),'complete canonical765 parent required'
    by={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(by)==len(old['source']) and old['comparisons'][-1]==(old['unit_register'],1)
    exports={k:old[k] for k in ACTIVE if k!='comparisons'}
    assert not set(CHANGED)&parent.parent.parent.parent.leaves(exports)
    for pre,pair in zip(PREFIXES,PAIRS):
        assert by[pre+'padded_A']==('+',pre+'scaled_A',12)
        assert by[pre+'input_A']==('+',pre+'F1',pre+'F3')
        assert by[pre+'scaled_A']==('*',16,'copies' if pre=='and__' else 'hist__joined_H__539')
        assert by[pre+'padded_B']==('+',pre+'scaled_B',10)
        assert by[pre+'input_B']==('+',pre+'F2',pre+'F3')
        assert (pre+'input_B',pre+'padded_B') in old['comparisons']
        assert by[pre+'F3']==('-' if pre=='and__' else '+',pre+'scaled_Z',8)
        assert by[pre+'scaled_Z']==('*',16,'Ahat' if pre=='and__' else 'hist__joined_Z__546')
        assert by[pre+'bs_q']==('-',pre+'q',pre+'bs_Q') and pre+'bs_q' in old['unit_factors']
        assert old['comparisons'].count(pair)==1
        assert not any(pair[1] in (a,b) for n,o,a,b in old['source'])
    assert not (set(FACTORS)|set(PRODUCTS))&by.keys()
    source=[(n,o,a,13 if n in CHANGED else b) for n,o,a,b in old['source']]
    unit=old['unit_register']
    for pair,factor,total in zip(PAIRS,FACTORS,PRODUCTS):
        source.extend([(factor,'-',pair[1],pair[0]),(total,'*',unit,factor)]);unit=total
    pairs=[v for v in old['comparisons'][:-1] if v not in PAIRS]+[(unit,1)]
    count=Counter(o for n,o,a,b in source);p=deepcopy(old)
    p.update(source=source,comparisons=pairs,unit_factors=old['unit_factors']+list(FACTORS),unit_register=unit,
             operations=len(source),multiplications=count['*'],additions_subtractions=count['+']+count['-'],equations=len(pairs),
             first_padding_parent=old,first_padding_units=list(FACTORS),
             first_padding_interfaces=[dict(prefix=pre,input=pair[0],shifted_padded=pair[1],
                                           padded_constant=13,parent_padded_constant=12,unit=factor)
                                       for pre,pair,factor in zip(PREFIXES,PAIRS,FACTORS)],
             identical_complete_integer_polynomial=False,identical_positive_zero_set=True,
             positive_zero_bijection=True,positive_zero_surjection=True,
             positive_zero_equality_scope='Full same-coordinate positive zeros for all positive program parameters, relative to the selected765 parent.',
             projection='Identity on supplied positive zeros. Both first-padding signs and both checksum signs are forced+1 locally before history typing; old G/H signs may stay negative.',
             positive_section='Identity on supplied positive zeros of the selected765 parent.')
    assert p['operations']==old['operations']+4 and p['equations']==old['equations']-2
    assert p['history_packet']==old['history_packet']
    return p


@lru_cache(None)
def _build(inline_initial,and_bounds,geometry_bounds):
    return rewrite(parent.build(inline_initial=inline_initial,and_bounds=and_bounds,geometry_bounds=geometry_bounds))


def build(*,inline_initial=True,and_bounds=True,geometry_bounds=True):
    return deepcopy(_build(*flags(inline_initial,and_bounds,geometry_bounds)))


def checked(packet):
    key=flags(*(packet.get(k) for k in ('inline_initial','and_bounds','geometry_bounds')))
    assert packet==_build(*key),'complete canonical first-padding763 packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.parent.parent.parent.polynomial_source(packet)


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.parent.parent.raw_degrees(packet)


def degree_audit(packet=None):
    if packet is None:packet=build()
    checked(packet);old=packet['first_padding_parent'];prior=parent.degree_audit(old)
    degree=degree_dictionary(packet);d=lambda n:degree[n] if isinstance(n,str) else 0
    assert all(degree[n]==v for n,v in parent.degree_dictionary(old).items())
    wanted=(2,4555 if packet['inline_initial'] else 135)
    for pre,pair,factor,w in zip(PREFIXES,PAIRS,FACTORS,wanted):
        assert d(factor)==d(pair[1])==d(pre+'scaled_A')==w>d(pair[0])
    assert ('hist__and__R10b','hist__and__R11') in packet['comparisons']
    assert d('hist__and__bs_packed')==prior['maximum_outer_degree']>max(wanted)
    assert max(max(d(a),d(b)) for a,b in packet['comparisons'][:-1])==prior['maximum_outer_degree']
    assert d(packet['unit_register'])==prior['unit_degree']+sum(wanted)
    rows,out=polynomial_source(packet)
    for n,o,a,b in rows:
        if n not in degree:degree[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    assert degree[out]==prior['exact_degree']+sum(wanted)
    return dict(exact_degree=degree[out],parent_exact_degree=prior['exact_degree'],degree_increment=sum(wanted),
                unit_degree=d(packet['unit_register']),maximum_outer_degree=prior['maximum_outer_degree'],
                first_padding_degrees=dict(zip(FACTORS,wanted)),
                exactness_reason='Each new factor has the strict nonzero leader16*leading(H). Old product leaders and the retained maximal first-index residual are unchanged; the anchored sum of real squares cannot cancel its top degree.')


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);count=Counter(o for n,o,a,b in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=count['*'],additions_subtractions=count['+']+count['-'],output=out),
                degree=degree_audit(packet))


def source_audit(cases=24):
    rng=random.Random(763765);count=Counter()
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo);old=p['first_padding_parent']
        rows,out=polynomial_source(p);before,target=parent.polynomial_source(old)
        for i in range(cases):
            signed=i>=cases//2
            values={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in p['parameters']+p['auxiliaries']}
            if i%6==0:values.update({f'hist__Shat{j}':1 for j in range(57)});count['zero_selector_contexts']+=1
            e=execute(rows,values);past=execute(before,values)
            assert all(e[n]==past[n]+int(n in CHANGED) for n,o,a,b in old['source'])
            for pair,f in zip(PAIRS,FACTORS):assert past[pair[0]]-past[pair[1]]==1-e[f]
            u=prod(e[f] for f in old['unit_factors']);a=prod(e[f] for f in FACTORS)
            at=lambda n:e[n] if isinstance(n,str) else n
            square=sum((at(x)-at(y))**2 for x,y in p['comparisons'][:-1]);deleted=sum((e[f]-1)**2 for f in FACTORS)
            assert e[out]==u*a*(1+square)-1 and past[target]==u*(1+square+deleted)-1
            assert e[out]-past[target]==u*((a-1)*(1+square)-deleted)
            count['complete_retained_register_maps']+=1;count['complete_output_corrections']+=1;count['signed_cases']+=signed
    return dict(count)


def leading_audit(packet,prime):
    rows,out=polynomial_source(packet);degree=degree_dictionary(packet)
    for n,o,a,b in rows:
        d=lambda z:degree[z] if isinstance(z,str) else 0
        if n not in degree:degree[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    top={n:(i+2) for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
    for pre in ('geo__','and__','hist__and__'):top[pre+'tau_gap']=top[pre+'eta']=top[pre+'zeta']=1
    for n,o,a,b in rows:
        da=degree[a] if isinstance(a,str) else 0;db=degree[b] if isinstance(b,str) else 0
        va=top[a] if isinstance(a,str) else a;vb=top[b] if isinstance(b,str) else b
        top[n]=(va*vb if o=='*' else (va if da==degree[n] else 0)+(1 if o=='+' else -1)*(vb if db==degree[n] else 0))%prime
        for pre in ('geo__','and__','hist__and__'):
            if n==pre+'R15':
                assert degree[n]==degree[pre+'cam2']+degree[pre+'gam']
                top[n]=2*top[pre+'cam2']*top[pre+'gam']%prime
    assert all(top[f] for f in packet['unit_factors']) and top[out]
    for pre,factor in zip(PREFIXES,FACTORS):assert top[factor]==top[pre+'scaled_A']
    return dict(prime=prime,degree=degree[out],output_leader_value=top[out],first_padding_leader_values={f:top[f] for f in FACTORS})


def population_audit():
    count=Counter();rng=random.Random(76316)
    for checksum,sign in product((1,-1),repeat=2):
        low3=8;low2=2;low1=(13-sign-low3)%16;low0=(-checksum-low1-low2-low3)%16
        lows=(low0,low1,low2,low3)
        assert lows=={(1,1):(1,4,2,8),(-1,1):(3,4,2,8),(1,-1):(15,6,2,8),(-1,-1):(1,6,2,8)}[(checksum,sign)]
        assert low0%2==1
        for t in range(4,19):
            q=1<<t;Q=q//16;highsum=(q-checksum-sum(lows))//16
            assert 16*highsum+sum(lows)==q-checksum
            if highsum<0:assert (checksum,sign,t)==(1,-1,4);count['impossible_small_scale']+=1;continue
            if t<=8:
                vectors=((a,b,c,highsum-a-b-c) for a in range(highsum+1) for b in range(highsum+1-a) for c in range(highsum+1-a-b))
            else:
                vectors=[]
                for _ in range(64):
                    cuts=sorted([0,highsum]+[rng.randrange(highsum+1) for _ in range(3)])
                    vectors.append(tuple(cuts[i+1]-cuts[i] for i in range(4)))
            for high in vectors:
                fields=tuple(16*a+b for a,b in zip(high,lows));assert sum(fields)==q-checksum and all(0<f<q for f in fields)
                r=sum(f*q**i for i,f in enumerate(fields));pop=r.bit_count()
                assert r>q and r>=9 and r%16==low0 and pop==sum(f.bit_count() for f in fields)
                lower=highsum.bit_count()+sum(a.bit_count() for a in lows);assert pop>=lower
                if (checksum,sign)!=(1,1):assert lower==(t+3 if (checksum,sign)==(1,-1) else t+1)>t;count['bad_sign_population_obstructions']+=1
                else:assert lower==t;count['allowed_sign_population_cases']+=1
                # Relaxed mod16 cone only: this least multiple of16 need not
                # be a multiple of q, as the complete source X must be.
                X=16*((r+15)//16);assert X>r
                for bound_sign in (-1,1):
                    beta=X-r-bound_sign
                    if beta>0:assert X-r==beta+bound_sign;count['positive_signed_bound_cases']+=1
                count['four_field_cases']+=1
    # A second-padding conversion has no corresponding population exclusion.
    fields=(1,20,36,8);q=64;r=sum(f*q**i for i,f in enumerate(fields))
    assert sum(fields)==q+1 and r.bit_count()==6 and fields[1]+fields[3]==16+12 and fields[2]+fields[3]==32+12
    return dict(count,second_padding_negative_component=dict(q=q,fields=fields,popcount=r.bit_count(),scope='Scalar fields only; not a compiled Pell zero.'),
                scope='Exhaustive high-field compositions for q16 through256, sampled larger dyadic scales; component sign obstructions, not complete compiled Pell tuples.')


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
    for pre in PREFIXES:
        for suffix in ('padded_A','input_A','scaled_A','padded_B','input_B','F3','scaled_Z','bs_q'):
            rows=[(n,o,a,17 if n==pre+suffix else b) for n,o,a,b in old['source']]
            reject(lambda rows=rows:rewrite(dict(old,source=rows)))
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo)
        for key,value in [('source',p['source'][:-1]),('comparisons',[]),('positive_zero_equality_scope','only inputs'),('first_padding_interfaces',[]),('unit_register','bad')]:
            for api in (polynomial_source,degree_audit,ledger):
                reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
        damaged=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo);damaged['source'].clear()
        assert build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo)==p
    for key in ('inline_initial','and_bounds','geometry_bounds'):reject(lambda key=key:build(**{key:1}))
    return count


def verify():
    forms=[]
    for inline,ands,geo in product((False,True),repeat=3):
        p=build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo);old=p['first_padding_parent']
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
    return dict(status='PASS_GPCP_FIRST_PADDING_UNITS763',forms=forms,source_audit=source_audit(),
                population_audit=population_audit(),rejected_callers=guards(),
                scope='Full same-coordinate positive-zero equality with selected765 parent for all positive program parameters. Old G/H signs may remain negative; no off-zero polynomial identity or complete Pell fixtures.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print({k:v for k,v in result.items() if k not in ('status','forms')})
