"""Encode the C2 delimiter by0 after the paid-prefix395 optimization.

Lettersabcde retain digits1..5. The literal query ends inaa, so appending
zero preserves the bounded-zero-run input proof. A shorter weighted-copy
prefix sum saves one A. Histories are recoded; no tuple identity is claimed.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import tseytin_copy_prefix395 as parent
import tseytin_c2_word_history as literal
import tseytin_universal425 as fusion
import tseytin_universal_factor_partitions as degree_helper

scale=parent.scale
execute=parent.execute
loader=fusion.loader
CODES={**loader.CODES,'#':0}
DELETED='linear_sum__380'
REQUIRED={
 'linear0_coefficient__50':('*',6,'selector_sum__8'),
 'linear_sum__380':('-','linear0_coefficient__50','selector_sum__7'),
 'linear_sum__381':('-','linear_sum__380','selector_sum__6'),
 'c2_shared_update_offset':('-','linear_sum__392',58328),
 'c2_terminal_product':('*',4096,'Ufinal'),
 'c2_terminal':('+','c2_terminal_product',3145)}


def raw(word):
    n=0
    for c in word:n=8*n+CODES[c]
    return n


def encode(word):return 8**len(word)+raw(word)


def maps():
    return [(8**len(a),raw(a),8**len(b),raw(b)) for a,b in literal.TILES]


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical395 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert all(rows.get(n)==v for n,v in REQUIRED.items())
    assert rows['query_numerator']==('-','query_last_product',-fusion.fused_coefficients()[0])
    assert {n for n,_,a,b in old['source'] if DELETED in (a,b)}=={'linear_sum__381'}
    changes={'linear0_coefficient__50':('*',5,'selector_sum__7'),
        'linear_sum__381':('-','linear0_coefficient__50','selector_sum__6'),
        'c2_shared_update_offset':('-','linear_sum__392',58322),
        'c2_terminal':('+','c2_terminal_product',73),
        'query_numerator':('-','query_last_product',-8*loader.COEFFICIENTS[0])}
    source=[(n,*changes.get(n,(o,a,b))) for n,o,a,b in old['source'] if n!=DELETED]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    # Keep only active scalar/compiler metadata. Earlier parent narratives
    # about same-tuple identities belong inside the historical parent.
    keys=('parameters','auxiliaries','comparisons','ordinary_comparisons',
          'unit_register','word_unit_register','power_unit_register',
          'word_factors','power_factors','merge_units','interfaces','program_recipe')
    p=scale.metadata(dict({k:deepcopy(old[k]) for k in keys},source=source,
        zero_delimiter_parent=old,zero_delimiter=True,letter_codes=CODES,
        positive_integer_domain=True,identical_complete_polynomial=False,
        identical_positive_zero_set=False,positive_zero_bijection=False,
        projection='On the same valid program slices, c2_initial=8*enc8(query); # has digit0. The complete accepted-input relation is preserved by recoded histories and fresh positive native extensions.'))
    assert p['operations']==old['operations']-1 and p['multiplications']==old['multiplications']
    assert p['additions_subtractions']==old['additions_subtractions']-1
    before=literal._history()['maps'];after=maps()
    assert all(tuple(a)==tuple(b) for i,(a,b) in enumerate(zip(before,after)) if i!=5)
    assert tuple(before[5])==(8,6,8,6) and after[5]==(8,0,8,0)
    assert max(max(a+c,b+d) for a,c,b,d in after)<65536
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(p):
    assert p==build(merge_units=p['merge_units']),'complete canonical zero-delimiter394 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    deg=degree_dictionary(packet);d=lambda v:deg[v] if isinstance(v,str) else 0
    for n,o,a,b in source:
        if n not in deg:deg[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=deg[out],word_factor_degree_bounds=[d(f) for f in packet['word_factors']],
        power_factor_degrees=[d(f) for f in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),
        exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    c=Counter(o for _,o,_,_ in source)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def modified_parent(source,values):
    """Explicit definition replay, not equality to the unmodified parent."""
    e=dict(values);at=lambda v:e[v] if isinstance(v,str) else v
    for n,o,a,b in source:
        if n=='linear0_coefficient__50':v=5*e['selector_sum__7']
        elif n==DELETED:v=e['linear0_coefficient__50']
        elif n=='c2_shared_update_offset':v=e['linear_sum__392']-58322
        elif n=='c2_terminal':v=4096*e['Ufinal']+73
        elif n=='query_numerator':v=e['query_last_product']+8*loader.COEFFICIENTS[0]
        else:
            x,y=at(a),at(b);v=x*y if o=='*' else x+y if o=='+' else x-y
        e[n]=v
    return e


def source_audit(cases=64):
    rng=random.Random(394396);totals=Counter();h=literal._history();actual=maps()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['zero_delimiter_parent']
      for case in range(cases):
        signed=case>=cases//2
        v={n:rng.randrange(-3,4) if signed else rng.randrange(1,4) for n in p['parameters']+p['auxiliaries']}
        if case%16==0:v.update({f'Shat{i}':1 for i in range(24)})
        e=execute(p['source'],v);other=modified_parent(old['source'],v)
        assert all(e[n]==other[n] for n,_,_,_ in p['source'])
        assert e['linear_sum__384']==sum((i+1)*v[f'Shat{i}'] for i in range(5))
        for tag,offset,out in [('U',1,'linear_constant__411'),('V',3,'linear_constant__430')]:
            expected=64*v[f'H_{tag}']
            expected+=sum(g['difference']*(v[f'Z{tag}hat{i}']-1) for i,g in enumerate(h['groups_'+tag]))
            expected+=sum(row[offset]*(v[f'Shat{i}']-1) for i,row in enumerate(actual))
            assert e[out]==expected
            totals['actual_map_update_identities']+=1
        for sos in (False,True):
            ns,no=polynomial_source(p,sum_of_squares=sos);os,oo=parent.polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,v)[no]==modified_parent(os,v)[oo]
            totals['complete_modified_parent_outputs']+=1;totals['signed_outputs']+=signed
    return dict(totals)


def query_audit():
    count=0;d=loader.DENOMINATOR;h=[8*c for c in loader.COEFFICIENTS]
    assert h[2]==h[5]==0
    for rank in (2,3,5):
      for relators in ((),((1,2,-1,-2),)):
        S=loader.program_word(rank,relators);A=fusion.program_parameter(S)
        for x in range(1,17):
            word=loader.query_word(S,x);assert word.endswith('aa')
            Q=8**(32*x);I=encode(word+'#')
            assert I==8*loader.encode(word)
            assert d*I==A*Q**6+sum(h[i]*Q**i for i in (0,1,3,4))
            assert max(map(len,bin(I)[2:].split('1')))<=4
            count+=1
    old=fusion.sign_filter();res=[]
    for case,basecase in zip(old['cases'],old['parent_exact_certificate']['cases']):
        Q=basecase['Q_residue'];R=sum(h[i]*pow(Q,i,d) for i in (0,1,3,4,6))%d
        assert 0<R<d and R==case['numerator_residue'];res.append(R)
    return dict(literal_query_cases=count,negative_power_branch_residues=res,
        zero_run_bound=4,denominator=d,tail_coefficients=h)


def encoding_audit():
    seen={};words=relations=0
    for length in range(6):
      for letters in product(literal.SYMBOLS,repeat=length):
        s=''.join(letters);n=encode(s);assert n not in seen;seen[n]=s
        assert len(oct(n)[2:])==length+1 and oct(n)[2]=='1'
        words+=1
    for k,(a,b) in enumerate(literal.RELATIONS):
      for direction in (0,1):
       for left,right in [('',''),('a','b'),('ed','c'),('aaa','bb')]:
        u,v=(a,b) if direction==0 else (b,a);start=left+u+right
        selection,end=literal.derivation_selection(start,[(k,direction,len(left))])
        top,bottom=literal.selected_words(selection)
        assert top+'#'+end==start+'#'+bottom
        U,V=1,encode(start+'#')
        for i in selection:
            aa,c,bb,d=maps()[i];U,V=aa*U+c,bb*V+d
        assert encode(top+'#'+end)==encode(start+'#'+bottom)
        assert U==encode(top) and V==encode(start+'#'+bottom)
        relations+=1
    # Genuine accepting histories, including multiple delimiter copies.
    fixtures=[]
    for start,steps in [('aaa',[]),('caaa',[(7,0,0)]),('dcaaa',[(7,0,1),(8,0,0)]),
                        ('ccaaa',[(7,0,1),(7,0,0)])]:
        selection,end=literal.derivation_selection(start,steps);assert end=='aaa'
        U,V=1,encode(start+'#')
        for i in selection:
            a,c,b,d=maps()[i];U,V=a*U+c,b*V+d
        assert V==4096*U+73
        fixtures.append(dict(word=start,tiles=list(selection),U=U,V=V,contains_delimiter=5 in selection))
    return dict(injective_sentinel_codes=words,actual_contextual_rewrites=relations,
        accepting_append_histories=fixtures,scope='Finite exact word/map fixtures, not full native Pell zeros.')


def guards():
    old=parent.build();bad=[dict(old,program_recipe='unrestricted'),dict(old,comparisons=[]),dict(old,interfaces={})]
    for name in REQUIRED|{'query_numerator':None}:
        bad.append(dict(old,source=[(n,o,a,7 if n==name else b) for n,o,a,b in old['source']]))
    bad.append(dict(old,source=old['source']+[('extra','+',DELETED,1)]))
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated parent accepted')
    total=len(bad)
    for key,val in [('letter_codes',literal.CODES),('projection','old delimiter'),('source',build()['source'][:-1])]:
      for api in (polynomial_source,degree_bound):
        try:api(dict(build(),**{key:val}))
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated successor accepted')
        total+=1
    return total


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);source,out=polynomial_source(p,sum_of_squares=sos);rec=ledger(p,sum_of_squares=sos)
        assert len(source)==(394 if merge else 396) and rec['polynomial']['multiplications']==182
        assert p['witnesses']==62 and p['equations']==(5 if merge else 6)
        fusion.baseline.closure(source,out,p['parameters']+p['auxiliaries'])
        before=parent.degree_dictionary(p['zero_delimiter_parent']);after=degree_dictionary(p)
        assert all(after[n]==v for n,v in before.items() if n!=DELETED)
        rec.update(merge_units=merge,sum_of_squares=sos,source=source,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_ZERO_DELIMITER394',forms=records,source_audit=source_audit(),
        query=query_audit(),encoding=encoding_audit(),rejected_callers=guards(),
        scope='Same universal accepted ordinary inputs on unchanged valid program numerals. Recode # to0 and rebuild positive histories/native witnesses; no same-coordinate zero-set or polynomial identity with395 claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit']);print(result['encoding'])
