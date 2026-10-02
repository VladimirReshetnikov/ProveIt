"""Type the upper initial digit before restoring its transport:383 ->381.

The new transport factor is +1 because -1 has residue B-1, outside the
typed history digit range [0,D). Full supplied positive zeros agree on
valid program slices. Complete polynomials need not agree off zero.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_cross_offsets383 as parent

scale=parent.scale
execute=parent.execute
PAIR=('U_lhs__151','U_rhs__155')
UPDATE='U_update__150'
TRANSPORT='upper_transport_unit'
WORD='upper_transport_word_unit'
REQUIRED={
    'U_lhs__151':('+',UPDATE,1),
    UPDATE:('*','B__3','linear_constant__411'),
    'U_rhs__155':('+','H_U','U_terminal__154'),
    'U_terminal__154':('*','P__30','Ufinal'),
    'B__3':('*','height_slack',65536),
    'P__30':('+','P_product__29',1),
    'P_product__29':('*','Bm1__28','J__27'),
    'Bm1__28':('-','B__3',1)}


def rewrite(old):
    global_unit=old.get('cross_offsets_global_unit');merge=old.get('merge_units')
    assert type(global_unit)is bool and type(merge)is bool
    assert old==parent.build(global_unit=global_unit,merge_units=merge),'complete canonical383/384 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(rows)==len(old['source']) and all(rows.get(n)==v for n,v in REQUIRED.items())
    assert old['ordinary_comparisons'].count(PAIR)==old['comparisons'].count(PAIR)==1
    assert not any(PAIR[0] in (a,b) for _,_,a,b in old['source'])
    active={k:old[k] for k in ('interfaces','parameters','auxiliaries','word_factors','power_factors',
                              'word_unit_register','power_unit_register','unit_register')}
    assert PAIR[0] not in parent.leaves(active)
    assert TRANSPORT not in rows and WORD not in rows
    source=[r for r in old['source'] if r[0]!=PAIR[0]]
    source.extend([(TRANSPORT,'-',PAIR[1],UPDATE),(WORD,'*',old['word_unit_register'],TRANSPORT)])
    if merge:
        assert rows[old['unit_register']]==('*',old['word_unit_register'],old['power_unit_register'])
        source=[(n,o,WORD,b) if n==old['unit_register'] else (n,o,a,b) for n,o,a,b in source]
    unit=old['unit_register'] if merge else WORD
    pairs=[(unit,1) if a==old['unit_register'] else (a,b) for a,b in old['comparisons'] if (a,b)!=PAIR]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=source,comparisons=pairs,
        ordinary_comparisons=[v for v in old['ordinary_comparisons'] if v!=PAIR],
        word_factors=old['word_factors']+[TRANSPORT],word_unit_register=WORD,unit_register=unit,
        upper_transport_parent=old,upper_transport_unit=True,upper_transport_register=TRANSPORT,
        identical_complete_polynomial=False,identical_positive_zero_set=True,
        identical_positive_zero_set_scope='full supplied positive zeros on valid recompiled program slices',
        positive_zero_bijection=True,positive_zero_bijection_scope='identity on every supplied coordinate on valid recompiled program slices',
        identity_reference=None,
        projection='Full supplied positive-zero equality with the selected383/384 parent on valid program slices. Type the history range before forcing the upper transport unit to +1.'))
    assert p['operations']==old['operations']+1 and p['equations']==old['equations']-1
    return p


@lru_cache(None)
def _build(global_unit,merge_units):
    return rewrite(parent.build(global_unit=global_unit,merge_units=merge_units))


def build(*,global_unit=True,merge_units=True):
    assert type(global_unit)is bool and type(merge_units)is bool
    return _build(global_unit,merge_units)


def checked_packet(packet):
    assert type(packet.get('cross_offsets_global_unit'))is bool and type(packet.get('merge_units'))is bool
    assert packet==build(global_unit=packet['cross_offsets_global_unit'],merge_units=packet['merge_units']),\
        'complete canonical upper-transport packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.parent.parent.parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.parent.parent.parent.parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet);d=lambda v:degrees[v] if isinstance(v,str) else 0
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),
        upper_transport_degree_bound=d(TRANSPORT),exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def source_audit(cases=64,seed=381383):
    rng=random.Random(seed);counts=Counter()
    for global_unit in (False,True):
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge);old=p['upper_transport_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%16==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_decoded_selector_contexts']+=1
            e=execute(p['source'],values);past=execute(old['source'],values)
            changed={PAIR[0]}|({old['unit_register']} if merge else set())
            assert all(e[n]==past[n] for n,_,_,_ in old['source'] if n not in changed)
            t=e[TRANSPORT];assert t==past[PAIR[1]]-past[PAIR[0]]+1
            W=prod(e[n] for n in old['word_factors']);E=prod(e[n] for n in old['power_factors'])
            assert e[WORD]==W*t
            at=lambda v:e[v] if isinstance(v,str) else v
            S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
            U=W*E if merge else W;Splus=S if merge else S+(E-1)**2
            for sos in (False,True):
                rows,out=polynomial_source(p,sum_of_squares=sos)
                before,target=parent.polynomial_source(old,sum_of_squares=sos)
                new=execute(rows,values)[out];prior=execute(before,values)[target]
                manual=(U*t-1)**2+Splus if sos else U*t*(1+Splus)-1
                correction=U*U*(t*t-1)-2*U*(t-1)-(t-1)**2 if sos else U*(t-1)*(Splus-t+2)
                assert new==manual and new-prior==correction
                counts['complete_parent_corrections_and_manual_outputs']+=1;counts['signed_outputs']+=signed
            counts['complete_retained_register_maps']+=1;counts['signed_register_maps']+=signed
    return dict(counts)


def residue_audit():
    """Independent typed-history boundary fixtures, not complete Pell zeros."""
    counts=Counter()
    for D in (1,2,3,8,17,64):
      B=65536*D
      for duration in (1,2,3,5):
        P=B**duration;J=(P-1)//(B-1)
        for digit in sorted({0,D//2,D-1}):
          for high in (0,J//B,max(0,(D-1)*J//B)):
            H=digit+B*high
            assert H%B==digit and 0<=digit<D<B-1
            for terminal in (1,3,101):
              for update in (0,1,H+terminal*P):
                t=H+P*terminal-B*update
                assert t%B==digit and t!=-1
                if abs(t)==1:assert t==1 and H%B==1
                counts['typed_residue_sign_exclusions']+=1
    # Positive upper histories with genuine affine step2x+1, including t=1.
    for duration in range(1,9):
        states=[1]
        for _ in range(duration):states.append(2*states[-1]+1)
        D=1
        while D<=max(states):D*=2
        B=65536*D;P=B**duration
        H=sum(states[j]*B**j for j in range(duration))
        NU=sum(states[j+1]*B**j for j in range(duration))
        assert H+P*states[-1]-B*NU==1
        assert all(0<=s<D for s in states)
        counts['genuine_positive_outer_transport_paths']+=1
    return dict(counts,scope='Scalar typed-history sign and positive outer transport checks; no claim of complete compiled Pell fixtures.')


def guards():
    count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    old=parent.build()
    for key,val in [('source',old['source'][:-1]),('comparisons',[]),('ordinary_comparisons',[]),
                    ('interfaces',{}),('auxiliaries',[]),('program_recipe','wrong'),('word_factors',[])]:
        reject(lambda key=key,val=val:rewrite(dict(old,**{key:val})))
    for name in REQUIRED:
        rows=[(n,o,a,17 if n==name else b) for n,o,a,b in old['source']]
        reject(lambda rows=rows:rewrite(dict(old,source=rows)))
    for global_unit in (False,True):
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge)
        for key,val in [('source',p['source'][:-1]),('comparisons',[]),('interfaces',{}),('word_factors',[]),
                        ('positive_zero_bijection_scope','all integer assignments')]:
          for api in (polynomial_source,degree_bound):
            reject(lambda key=key,val=val,api=api:api(dict(p,**{key:val})))
    for key in ('global_unit','merge_units'):reject(lambda key=key:build(**{key:1}))
    return count


def verify():
    forms=[]
    for global_unit in (False,True):
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge)
        for sos in (False,True):
            rows,out=polynomial_source(p,sum_of_squares=sos);record=ledger(p,sum_of_squares=sos)
            lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=[out]
            while todo:
                n=todo.pop()
                if isinstance(n,str) and n in lookup and n not in seen:seen.add(n);todo.extend(lookup[n])
            assert seen==lookup.keys()
            old=parent.ledger(p['upper_transport_parent'],sum_of_squares=sos)
            assert record['polynomial']['operations']==old['polynomial']['operations']-2
            assert record['polynomial']['multiplications']==old['polynomial']['multiplications']==176
            assert record['polynomial']['additions_subtractions']==old['polynomial']['additions_subtractions']-2
            assert record['polynomial']['upper_transport_degree_bound']==3
            record.update(global_unit=global_unit,merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_UPPER_TRANSPORT_UNIT381',forms=forms,source_audit=source_audit(),
        residue_audit=residue_audit(),rejected_callers=guards(),
        scope='Full supplied positive-zero equality with the selected383/384 parent on valid recompiled program slices; no off-zero polynomial identity or exact-degree claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit']);print(result['residue_audit'])
