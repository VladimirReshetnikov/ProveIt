"""A shifted initial word and delimiter balance reduce upper-transport381 to380.

The supplied c2_initial now means the literal initial encoding minus one.
Positive zeros correspond affinely on valid recompiled program slices;
complete polynomials differ off zero by the audited finalizer corrections.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path
import random

import tseytin_upper_transport_unit381 as parent
import tseytin_permuted_digits387 as code

scale=parent.scale
execute=parent.execute
DENOMINATOR=code.loader.DENOMINATOR
PAIR=('V_lhs__153','V_rhs__157')
TRANSPORT='lower_transport_unit'
WORD='lower_transport_word_unit'
QUERY_CONSTANT=1345989957830772546645359926868824453377730675082689163408901
REQUIRED={
    'V_lhs__153':('+','V_update__152','c2_initial'),
    'V_update__152':('*','B__3','linear_constant__430'),
    'V_rhs__157':('+','H_V','V_terminal__156'),
    'V_terminal__156':('*','P__30','c2_terminal'),
    'c2_terminal':('+','c2_terminal_product',2560),
    'c2_terminal_product':('*',4096,'Ufinal'),
    'query_scaled_word':('*',DENOMINATOR,'c2_initial'),
    'query_numerator':('-','query_last_product',QUERY_CONSTANT),
    'B__3':('*','height_slack',65536),
    'P__30':('+','P_product__29',1),
    'P_product__29':('*','Bm1__28','J__27'),
    'Bm1__28':('-','B__3',1)}
INITIAL_CONSUMERS={'V_lhs__153','query_scaled_word'}


def rewrite(old):
    global_unit=old.get('cross_offsets_global_unit');merge=old.get('merge_units')
    assert type(global_unit)is bool and type(merge)is bool
    assert old==parent.build(global_unit=global_unit,merge_units=merge),'complete canonical381 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(rows)==len(old['source']) and all(rows.get(n)==v for n,v in REQUIRED.items())
    assert {n for n,_,a,b in old['source'] if 'c2_initial' in (a,b)}==INITIAL_CONSUMERS
    assert old['interfaces']['initial']=='c2_initial'
    assert old['ordinary_comparisons'].count(PAIR)==old['comparisons'].count(PAIR)==1
    assert old['ordinary_comparisons'].count(('query_numerator','query_scaled_word'))==1
    assert TRANSPORT not in rows and WORD not in rows
    source=[]
    if merge:assert rows[old['unit_register']]==('*',old['word_unit_register'],old['power_unit_register'])
    for n,o,a,b in old['source']:
        if n=='query_numerator':b+=DENOMINATOR
        if merge and n==old['unit_register']:a=WORD
        source.append((n,o,a,b))
    source.extend([(TRANSPORT,'-',PAIR[1],PAIR[0]),(WORD,'*',old['word_unit_register'],TRANSPORT)])
    unit=old['unit_register'] if merge else WORD
    pairs=[(unit,1) if a==old['unit_register'] else (a,b) for a,b in old['comparisons'] if (a,b)!=PAIR]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    interfaces=dict(old['interfaces']);del interfaces['initial'];interfaces['initial_minus_one']='c2_initial'
    p=scale.metadata(dict(old,source=source,comparisons=pairs,interfaces=interfaces,
        ordinary_comparisons=[v for v in old['ordinary_comparisons'] if v!=PAIR],
        word_factors=old['word_factors']+[TRANSPORT],word_unit_register=WORD,unit_register=unit,
        lower_transport_parent=old,lower_transport_unit=True,lower_transport_register=TRANSPORT,
        literal_initial_relation='literal base8 initial encoding = c2_initial + 1',
        program_recipe=old['program_recipe']+' The supplied c2_initial is enc_new(query+#)-1; its paid query numerator is the historical numerator minus d.',
        identical_complete_polynomial=False,identical_positive_zero_set=False,
        identical_positive_zero_set_scope=None,
        positive_zero_bijection=True,
        positive_zero_bijection_scope='On valid recompiled program slices: parent c2_initial = new c2_initial + 1; every other supplied coordinate unchanged.',
        identity_reference=None,
        projection='Shift the initial coordinate by +1. After independent native and upper-sign restoration, recover either query+# or query+b from the lower unit. Delimiter balance excludes query+b, then the global sign is positive.'))
    assert p['operations']==old['operations']+2 and p['equations']==old['equations']-1
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
        'complete canonical lower-transport packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    assert type(sum_of_squares)is bool
    checked_packet(packet)
    return parent.parent.parent.parent.parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.parent.parent.parent.parent.parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet);d=lambda v:degrees[v] if isinstance(v,str) else 0
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),
        lower_transport_degree_bound=d(TRANSPORT),exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def source_audit(cases=48,seed=380381):
    rng=random.Random(seed);counts=Counter()
    for global_unit in (False,True):
      for merge in (False,True):
        p=build(global_unit=global_unit,merge_units=merge);old=p['lower_transport_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%12==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_decoded_selector_contexts']+=1
            lifted=dict(values,c2_initial=values['c2_initial']+1)
            e=execute(p['source'],values);past=execute(old['source'],lifted)
            shifts={PAIR[0]:1,'query_scaled_word':DENOMINATOR,'query_numerator':DENOMINATOR}
            assert all(past[n]==e[n]+shifts.get(n,0) for n,_,_,_ in old['source'] if not (merge and n==old['unit_register']))
            ell=e[TRANSPORT];assert past[PAIR[0]]-past[PAIR[1]]==1-ell
            W=prod(e[n] for n in old['word_factors']);E=prod(e[n] for n in old['power_factors'])
            assert e[WORD]==W*ell
            at=lambda v:e[v] if isinstance(v,str) else v
            S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
            U=W*E if merge else W;Splus=S if merge else S+(E-1)**2
            for sos in (False,True):
                rows,out=polynomial_source(p,sum_of_squares=sos)
                before,target=parent.polynomial_source(old,sum_of_squares=sos)
                new=execute(rows,values)[out];prior=execute(before,lifted)[target]
                manual=(U*ell-1)**2+Splus if sos else U*ell*(1+Splus)-1
                correction=U*U*(ell*ell-1)-2*U*(ell-1)-(ell-1)**2 if sos else U*(ell-1)*(Splus-ell+2)
                assert new==manual and new-prior==correction
                counts['complete_affine_parent_corrections_and_manual_outputs']+=1;counts['signed_outputs']+=signed
            counts['complete_affine_retained_register_maps']+=1;counts['signed_register_maps']+=signed
    return dict(counts)


def word_audit():
    """Literal query/radix/delimiter tests; these are not complete Pell zeros."""
    counts=Counter()
    codes={'a':0,'b':3,'c':1,'d':2,'e':4,'#':5}
    assert code.CODES==codes and tuple(code.TILES)==tuple(build()['tiles'])
    def enc(word):
        n=1
        for c in word:n=8*n+codes[c]
        return n
    def query(S,x):
        return S+'a'+('a'+'b'*63)*x+'abb'+('a'+'b'*31)*x+'abb'+('a'+'b'*63)*x+'abbb'+('a'+'b'*31)*x+'abbb'+'aa'
    def max_zero(n):return max(map(len,bin(n)[2:].split('1')))
    for u,v in code.TILES:
        assert u.count('#')==v.count('#');counts['literal_tile_delimiter_balances']+=1
    coeff=code.fused_coefficients()
    for length in range(1,5):
      for letters in product('cd',repeat=length):
       S=''.join(letters);A=code.program_parameter(S)
       for x in range(1,9):
        w=query(S,x);assert w==code.loader.query_word(S,x) and '#' not in w and 'aaa' not in w
        Q=8**(32*x)
        N=A*Q**6+sum(coeff[j]*Q**j for j in range(6))
        old=enc(w+'#');new=old-1
        assert N==DENOMINATOR*old and N-DENOMINATOR==DENOMINATOR*new and new>0
        assert enc(w+'b')==old-2
        counts['literal_queries_and_affine_initials']+=1
        for sign in (-1,1):
            effective=new+sign
            assert effective==enc(w+('#' if sign==1 else 'b')) and effective>0 and max_zero(effective)<=10
            counts['signed_initial_zero_run_bounds']+=1
            powers=sorted(set(range(0,effective.bit_length()+1,17))|{0,1,2,15,16,17,effective.bit_length()})
            for power in powers:
                D=1<<power;B=65536*D
                if effective>=B:assert effective%B>=D
                if effective%B<D:assert effective<D
                counts['initial_wrap_exclusions']+=1
        for duration in (1,2,7,24):
            selected=[code.TILES[(x+length+5*j)%24] for j in range(duration)]
            top=''.join(t[0] for t in selected);bottom=''.join(t[1] for t in selected)
            assert (w+'b'+bottom).count('#')+1==(top+'#aaa').count('#')
            assert enc(w+'b'+bottom)!=enc(top+'#aaa')
            assert enc(top+'#aaa')==4096*enc(top)+2560
            counts['negative_delimiter_word_obstructions']+=1
    # The shifted numerator has exactly the old residues at both wrong powers.
    wrong=[]
    for parity in (0,1):
        q=pow(2,96*parity,DENOMINATOR)*pow(16,-1,DENOMINATOR)%DENOMINATOR
        r=sum(coeff[j]*pow(q,j,DENOMINATOR) for j in range(7))%DENOMINATOR
        assert r and (r-DENOMINATOR)%DENOMINATOR==r;wrong.append(r)
    assert wrong==[29966043244819123951156626953424814080,45854471631935696494459945720637767680]
    return dict(counts,wrong_power_residues=wrong,
        scope='Literal query, affine initial, typed radix and delimiter components, not complete compiled Pell zeros.')


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
                        ('positive_zero_bijection_scope','all integer assignments'),('literal_initial_relation','unshifted')]:
          for api in (polynomial_source,degree_bound):
            reject(lambda key=key,val=val,api=api:api(dict(p,**{key:val})))
        for key in ('cross_offsets_global_unit','merge_units'):
            reject(lambda key=key:polynomial_source(dict(p,**{key:int(p[key])})))
    for key in ('global_unit','merge_units'):reject(lambda key=key:build(**{key:1}))
    reject(lambda:polynomial_source(sum_of_squares=1))
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
            old=parent.ledger(p['lower_transport_parent'],sum_of_squares=sos)
            assert record['polynomial']['operations']==old['polynomial']['operations']-1
            assert record['polynomial']['multiplications']==old['polynomial']['multiplications']==176
            assert record['polynomial']['additions_subtractions']==old['polynomial']['additions_subtractions']-1
            assert record['polynomial']['lower_transport_degree_bound']==3
            assert p['parameters']==p['lower_transport_parent']['parameters'] and p['auxiliaries']==p['lower_transport_parent']['auxiliaries']
            assert 'initial' not in p['interfaces'] and p['interfaces']['initial_minus_one']=='c2_initial'
            record.update(global_unit=global_unit,merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],interfaces=p['interfaces'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_LOWER_TRANSPORT_UNIT380',forms=forms,source_audit=source_audit(),
        word_audit=word_audit(),rejected_callers=guards(),
        scope='Positive-zero affine bijection to the selected381 parent on valid recompiled program slices: old initial = new initial + 1. No off-zero polynomial identity or exact-degree claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit']);print(result['word_audit'])
