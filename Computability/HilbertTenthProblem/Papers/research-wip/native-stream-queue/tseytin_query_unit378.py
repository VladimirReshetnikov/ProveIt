"""The paid query residue forces its unit sign: complete C2 380 ->378.

Fold +1 into an existing fixed subtraction. On valid program slices the
two wrong exponent residues exclude both query-unit signs, and the correct
branch forces +1. No ordinary comparison remains in the default source.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_lower_transport_unit380 as parent
import tseytin_permuted_digits387 as encoding
import pell_fixed_affine_exponent52 as exponent
import native_binary_norm_units as norms
import tseytin_universal_factor_partitions as degrees_helper

scale,execute=parent.scale,parent.execute
PAIR=('query_numerator','query_scaled_word')
QUERY='query_unit'
WORD='query_word_unit'
D=parent.DENOMINATOR


def rewrite(old):
    global_unit=old.get('cross_offsets_global_unit');merge=old.get('merge_units')
    assert type(global_unit)is bool and type(merge)is bool
    assert old==parent.build(global_unit=global_unit,merge_units=merge),'complete canonical lower380 parent required'
    by={n:(o,a,b) for n,o,a,b in old['source']}
    assert by['query_numerator']==('-','query_last_product',parent.QUERY_CONSTANT+D)
    assert by['query_scaled_word']==('*',D,'c2_initial')
    assert not any(PAIR[0] in (a,b) for n,o,a,b in old['source'])
    assert old['ordinary_comparisons'].count(PAIR)==old['comparisons'].count(PAIR)==1
    assert old['interfaces']['initial_minus_one']=='c2_initial' and 'initial' not in old['interfaces']
    assert QUERY not in by and WORD not in by
    if merge:assert by[old['unit_register']]==('*',old['word_unit_register'],old['power_unit_register'])
    source=[]
    for n,o,a,b in old['source']:
        if n==PAIR[0]:b-=1
        if merge and n==old['unit_register']:a=WORD
        source.append((n,o,a,b))
    source.extend([(QUERY,'-',*PAIR),(WORD,'*',old['word_unit_register'],QUERY)])
    unit=old['unit_register'] if merge else WORD
    pairs=[(unit,1) if a==old['unit_register'] else (a,b) for a,b in old['comparisons'] if (a,b)!=PAIR]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    result=scale.metadata(dict(old,source=source,comparisons=pairs,
        ordinary_comparisons=[v for v in old['ordinary_comparisons'] if v!=PAIR],
        word_factors=old['word_factors']+[QUERY],word_unit_register=WORD,unit_register=unit,
        query_unit_parent=old,query_unit_register=QUERY,query_unit_enabled=True,
        query_numerator_added_constant=1,
        program_recipe=old['program_recipe']+' The current query_numerator additionally includes +1, folded into its fixed subtraction; query_unit=1 restores the paid shifted-initial query.',
        identical_complete_polynomial=False,identical_positive_zero_set=True,
        identical_positive_zero_set_scope='full supplied positive zeros on valid recompiled program slices',
        positive_zero_bijection=True,
        positive_zero_bijection_scope='identity on all supplied coordinates on valid recompiled program slices',
        identity_reference=None,
        projection='The individual exponent units give its signed power projection. Exact query residues then force the correct power and query_unit=+1, before any history or transport interpretation; the complete380 parent is restored on the same tuple.'))
    assert result['operations']==old['operations']+2 and result['equations']==old['equations']-1
    return result


@lru_cache(None)
def _build(global_unit,merge_units):return rewrite(parent.build(global_unit=global_unit,merge_units=merge_units))


def build(*,global_unit=True,merge_units=True):
    assert type(global_unit)is bool and type(merge_units)is bool
    return _build(global_unit,merge_units)


def checked_packet(packet):
    assert type(packet.get('cross_offsets_global_unit'))is bool and type(packet.get('merge_units'))is bool
    assert packet==build(global_unit=packet['cross_offsets_global_unit'],merge_units=packet['merge_units']),\
        'complete canonical query-unit packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    assert type(sum_of_squares)is bool;checked_packet(packet)
    if len(packet['comparisons'])==1 and not sum_of_squares:
        assert packet['comparisons']==[(packet['unit_register'],1)]
        assert not packet['ordinary_comparisons'] and packet['merge_units']
        assert 'query_unit_output' not in {n for n,o,a,b in packet['source']}
        return list(packet['source'])+[('query_unit_output','-',packet['unit_register'],1)],'query_unit_output'
    return norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return degrees_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet);d=lambda n:degrees[n] if isinstance(n,str) else 0
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        maximum_ordinary_residual_degree=max((max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),default=0),
        query_unit_degree_bound=d(QUERY),exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for n,o,a,b in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def source_audit(cases=48,seed=378380):
    rng=random.Random(seed);counts=Counter()
    for global_unit in (False,True):
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge);old=p['query_unit_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%12==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_selector_contexts']+=1
            e=execute(p['source'],values);past=execute(old['source'],values)
            changed={PAIR[0]}|({old['unit_register']} if merge else set())
            assert all(e[n]==past[n] for n,o,a,b in old['source'] if n not in changed)
            assert e[PAIR[0]]==past[PAIR[0]]+1
            t=e[QUERY];assert t==past[PAIR[0]]-past[PAIR[1]]+1
            W=prod(past[n] for n in old['word_factors']);E=prod(past[n] for n in old['power_factors'])
            U=W*E if merge else W
            at=lambda n:e[n] if isinstance(n,str) else n
            S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
            Splus=S if merge else S+(E-1)**2
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
    p=build();by={n:(o,a,b) for n,o,a,b in p['source']}
    rename=lambda n:('exp__'+n if isinstance(n,str) and n!='x' else n)
    expected={rename(n):(o,rename(a),rename(b)) for n,o,a,b in exponent.build()['source']}
    assert all(by[n]==v for n,v in expected.items())
    assert p['power_factors']==[rename(n) for n in exponent.build()['unit_factors']]
    assert D==2**192-1
    h=encoding.fused_coefficients();wrong=[]
    for parity in (0,1):
        q=pow(2,96*parity,D)*pow(16,-1,D)%D
        residue=sum(h[j]*pow(q,j,D) for j in range(7))%D
        closed=24*((15759360*2**96+558888960) if parity==0 else (24115200*2**96+550533120))
        assert residue==closed and 0<residue<D-2
        assert (residue-D)%D==residue
        wrong.append(residue)
    count=0
    for S in ('c','d','cd','dcc','ccdd'):
      A=encoding.program_parameter(S)
      for x in range(1,17):
        q=2**(96*x);I=encoding.encode(encoding.loader.query_word(S,x)+'#')-1
        N=A*q**6+sum(h[j]*q**j for j in range(6))-D
        assert I>0 and N==D*I and N+1-D*I==1
        badq=2**(96*x-4)
        bad=(A*badq**6+sum(h[j]*badq**j for j in range(6))-D)%D
        assert bad==wrong[x%2] and bad not in (0,D-2)
        count+=1
    return dict(unchanged_exponent_source_rows=len(expected),literal_query_cases=count,
        wrong_power_residues=wrong,wrong_power_allowed_residues=[0,D-2],
        scope='Exact two-parity modular certificate and literal query checks; the full signed exponent theorem supplies the unbounded necessary branches.')


def guards():
    count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    old=parent.build()
    for key,value in [('source',old['source'][:-1]),('comparisons',[]),('interfaces',{}),('auxiliaries',[]),
                      ('program_recipe','wrong'),('word_factors',[]),('literal_initial_relation','unshifted')]:
        reject(lambda key=key,value=value:rewrite(dict(old,**{key:value})))
    for g in (False,True):
      for m in (False,True):
        p=build(global_unit=g,merge_units=m)
        for key,value in [('source',p['source'][:-1]),('comparisons',[]),('interfaces',{}),
                          ('query_numerator_added_constant',0),('positive_zero_bijection_scope','all integer assignments')]:
          for api in (polynomial_source,degree_bound):
            reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
        for key in ('cross_offsets_global_unit','merge_units'):
            reject(lambda key=key:polynomial_source(dict(p,**{key:int(p[key])})))
    for key in ('global_unit','merge_units'):reject(lambda key=key:build(**{key:1}))
    reject(lambda:polynomial_source(sum_of_squares=1))
    return count


def verify():
    forms=[]
    for g in (False,True):
      for m in (False,True):
        p=build(global_unit=g,merge_units=m)
        for sos in (False,True):
            rows,out=polynomial_source(p,sum_of_squares=sos);record=ledger(p,sum_of_squares=sos)
            by={n:(a,b) for n,o,a,b in rows};todo=[out];seen=set()
            while todo:
                n=todo.pop()
                if isinstance(n,str) and n in by and n not in seen:seen.add(n);todo.extend(by[n])
            assert seen==by.keys()
            old=parent.ledger(p['query_unit_parent'],sum_of_squares=sos)
            special=g and m and not sos
            assert record['polynomial']['operations']==old['polynomial']['operations']-(2 if special else 1)
            assert record['polynomial']['multiplications']==176-int(special)
            assert record['polynomial']['query_unit_degree_bound']==7
            record.update(global_unit=g,merge_units=m,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_QUERY_UNIT378',forms=forms,source_audit=source_audit(),
        residue_audit=residue_audit(),rejected_callers=guards(),
        scope='Full supplied positive-zero equality with lower380 on valid recompiled program slices. Default all-unit source is its complete product minus1. No off-zero identity or exact-degree claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit']);print(result['residue_audit'])
