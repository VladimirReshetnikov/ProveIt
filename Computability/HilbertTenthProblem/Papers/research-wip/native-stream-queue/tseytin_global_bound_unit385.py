"""Move the positive global bound into the unit product:386 ->385.

The reserved binary digits exclude the negative native index unit before
using the global unit's sign. Positive zeros correspond by beta_old=beta+1
on valid program slices. This is not an off-zero polynomial identity.
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

import tseytin_shared_offsets386 as parent

scale=parent.scale
execute=parent.execute
GLOBAL_PAIR=('global_lhs__40','P__30')
G='global_bound_unit'
WORD='global_word_unit'
PORTS=['H_U','H_V']+[f'Z{side}hat{i}' for side in ('U','V') for i in range(4)]


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge)is bool and old==parent.build(merge_units=merge),'complete canonical386 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert rows['global_lhs__40']==('+','global_bound','global_sum__39')
    assert {n for n,_,a,b in old['source'] if 'global_bound' in (a,b)}=={'global_lhs__40'}
    assert not any('global_bound' in pair for pair in old['comparisons'])
    assert old['ordinary_comparisons'].count(GLOBAL_PAIR)==old['comparisons'].count(GLOBAL_PAIR)==1
    assert G not in rows and WORD not in rows
    source=list(old['source'])+[(G,'-',GLOBAL_PAIR[1],GLOBAL_PAIR[0]),(WORD,'*',old['word_unit_register'],G)]
    if merge:
        assert rows[old['unit_register']]==('*',old['word_unit_register'],old['power_unit_register'])
        source=[(n,o,WORD,b) if n==old['unit_register'] else (n,o,a,b) for n,o,a,b in source]
    unit=old['unit_register'] if merge else WORD
    pairs=[(unit,1) if a==old['unit_register'] else (a,b) for a,b in old['comparisons'] if (a,b)!=GLOBAL_PAIR]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=source,comparisons=pairs,
        ordinary_comparisons=[v for v in old['ordinary_comparisons'] if v!=GLOBAL_PAIR],
        word_unit_register=WORD,unit_register=unit,word_factors=old['word_factors']+[G],
        global_unit_parent=old,global_bound_unit=True,global_unit_register=G,
        identical_complete_polynomial=False,identical_positive_zero_set=False,
        positive_zero_bijection=True,positive_zero_bijection_scope='valid recompiled program slices; beta_parent=beta_new+1',
        identity_reference=None,projection='Full positive-zero bijection with386 on valid program slices by global_bound_parent=global_bound_new+1, retaining every other coordinate.'))
    assert p['operations']==old['operations']+2 and p['equations']==old['equations']-1
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical global-unit385 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.parent.parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


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


def parent_values(values):return dict(values,global_bound=values['global_bound']+1)


def source_audit(cases=80):
    rng=random.Random(385386);counts=Counter()
    for merge in (False,True):
        p=build(merge_units=merge);old=p['global_unit_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-4,5) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            e=execute(p['source'],values);past=execute(old['source'],parent_values(values))
            changed={'global_lhs__40'}|({old['unit_register']} if merge else set())
            assert all(e[n]==past[n] for n,_,_,_ in old['source'] if n not in changed)
            assert past['global_lhs__40']==e['global_lhs__40']+1
            assert e[G]==e['P__30']-sum(e[n] for n in PORTS)-values['global_bound']
            W=prod(e[n] for n in old['word_factors']);E=prod(e[n] for n in old['power_factors']);g=e[G]
            assert e[WORD]==W*g
            at=lambda v:e[v] if isinstance(v,str) else v
            S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
            U=W*E if merge else W;Splus=S if merge else S+(E-1)**2
            for sos in (False,True):
                rows,out=polynomial_source(p,sum_of_squares=sos)
                prior,target=parent.polynomial_source(old,sum_of_squares=sos)
                new=execute(rows,values)[out];prior=execute(prior,parent_values(values))[target]
                manual=(U*g-1)**2+Splus if sos else U*g*(1+Splus)-1
                difference=U*U*(g*g-1)-2*U*(g-1)-(g-1)**2 if sos else U*(g-1)*(Splus-g+2)
                assert new==manual and new-prior==difference
                counts['complete_parent_difference_and_manual_outputs']+=1;counts['signed_outputs']+=signed
            counts['complete_retained_register_maps']+=1;counts['signed_register_maps']+=signed
    return dict(counts)


def scalar_audit():
    p=build();counts=Counter()
    for D in (1,2,3,8):
      for J in (1,2,5):
       for tile in (0,5,8,14,23):
        B=65536*D;P=(B-1)*J+1
        for port in PORTS:
         for sign in (-1,1):
            values={n:1 for n in p['parameters']+p['auxiliaries']}
            values['height_slack']=D;values[f'Shat{tile}']=J+1
            # Attain Sigma=P on the negative-unit branch; Sigma=P-2 on +.
            values[port]=P-9-(2 if sign==1 else 0)
            Sigma=sum(values[n] for n in PORTS);values['global_bound']=P-Sigma-sign
            assert min(values.values())>0 and Sigma<=P
            e=execute(p['source'],values);T=P**34
            assert e[G]==sign and e['P__30']==P
            H0,M0,Z=(e[n] for n in ('joined_H__286','joined_M__292','joined_Z__294'))
            assert all(0<=v<T for v in (H0,M0,Z))
            H,M=H0+2*T,M0+T;q=16*B*T
            F=[q-16*H-12-16*M-10+16*Z+8-1,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
            assert sum(F)==q-1 and F[0]>2 and all(0<v<q for v in F)
            assert [v%16 for v in F]==[1,4,2,8]
            r=sum(v*q**i for i,v in enumerate(F))
            assert e['and__bs_packed']==r and r-2>q and e['and__wn2']>r
            counts['signed_global_unit_pretyping_contexts']+=1
            counts['height_one_contexts']+=D==1;counts['Sigma_equals_P_contexts']+=sign==-1
    for D in range(1,9):
      for J in range(1,20):
        P=(65536*D-1)*J+1
        Sigma_upper=4*(D-1)*J+8
        assert P-Sigma_upper==(65532*D+3)*J-7>1
        counts['parent_slack_margins']+=1
    return dict(counts)


def reserved_bits_audit():
    counts=Counter()
    for t in range(5,11):
        q=1<<t;Q=q//16
        for a in range(Q-1):
          for b in range(Q-1-a):
            for c in range(Q-1-a-b):
                d=Q-2-a-b-c
                high=[a,b,c,d];fields=[16*v+r for v,r in zip(high,[15,4,2,8])]
                rho=sum(v*q**i for i,v in enumerate(fields))
                assert sum(fields)==q-3 and all(0<v<q for v in fields)
                population=sum(v.bit_count() for v in fields)
                assert population==rho.bit_count()==sum(v.bit_count() for v in high)+7
                assert population>t and sum(v.bit_count() for v in high)>=(Q-2).bit_count()==t-5
                counts['negative_index_reserved_bit_cases']+=1
    return dict(counts,scope='Exhaustive high-field compositions for q=2^5 through2^10; the general proof uses popcount subadditivity.')


def guards():
    count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed packet accepted')
    old=parent.build()
    for key,val in [('source',old['source'][:-1]),('comparisons',[]),('program_recipe','wrong'),('auxiliaries',[]),('word_factors',[])]:
        reject(lambda key=key,val=val:rewrite(dict(old,**{key:val})))
    p=build()
    for key,val in [('source',p['source'][:-1]),('comparisons',[]),('positive_zero_bijection_scope','everywhere'),('word_factors',[])]:
        for api in (polynomial_source,degree_bound):reject(lambda key=key,val=val,api=api:api(dict(p,**{key:val})))
    return count


def verify():
    forms=[]
    for merge in (False,True):
        p=build(merge_units=merge)
        for sos in (False,True):
            rows,out=polynomial_source(p,sum_of_squares=sos);record=ledger(p,sum_of_squares=sos)
            lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=[out]
            while todo:
                n=todo.pop()
                if isinstance(n,str) and n in lookup and n not in seen:seen.add(n);todo.extend(lookup[n])
            assert seen==lookup.keys()
            assert record['polynomial']['operations']==(385 if merge else 387)
            assert record['polynomial']['multiplications']==178
            assert record['polynomial']['additions_subtractions']==(207 if merge else 209)
            assert record['polynomial']['degree_upper_bound']==(9400 if sos else 4714) if merge else record['polynomial']['degree_upper_bound']==(9292 if sos else 4754)
            assert p['witnesses']==62 and degree_dictionary(p)[G]==2
            record.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_GLOBAL_BOUND_UNIT385',forms=forms,
        source_audit=source_audit(),scalar_audit=scalar_audit(),reserved_bits=reserved_bits_audit(),
        rejected_callers=guards(),scope='Full positive-zero bijection on valid program slices via global_bound_parent=global_bound_new+1. Numerical fixtures are source/components, not complete compiled Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print({k:v for k,v in result.items() if k not in ('forms','status')})
