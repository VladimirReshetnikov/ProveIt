"""Twelve exact additions/subtractions saved in C2 word and universal sources.

Eight paid selector blocks share the chronological sum (11A); one paid
constant offset is shared between the two update words (1A). All supplied
coordinates, complete polynomials and degree dictionaries are unchanged.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_universal440 as universal

word=universal.word
execute=word.execute
scale=word.scale
TERMS=('selector_sum__8','linear_group__362','linear_group__364',
       'linear_group__366','linear_group__368','group_sum__223',
       'group_sum__230','linear_group__374')
SUPPORTS=((0,1,2,3,4,5),(6,7),(8,9),(10,11),(12,13),
          (14,16,21,23),(15,17,20,22),(18,19))
SUM='selector_sum__26'
DELETED={f'selector_sum__{i}' for i in range(9,26)}|{'linear_shared_sum__410','linear_shared_sum__429'}
SHIFT='c2_shared_update_offset'
PUBLIC_KEYS=('parameters','auxiliaries','comparisons','ordinary_comparisons','outer_pairs',
    'unit_register','unit_factors','word_unit_register','power_unit_register','word_factors',
    'power_factors','interfaces','public_registers','canonical_native_registers',
    'private_restoration_coordinates','group_products')


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):value=value.values()
    elif not isinstance(value,(list,tuple,set)):return set()
    return set().union(*(leaves(v) for v in value))


def support_rows(old):
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    selectors={f'Shat{i}':frozenset((i,)) for i in range(24)}
    @lru_cache(None)
    def support(n):
        if n in selectors:return selectors[n]
        o,a,b=rows[n];assert o=='+' and isinstance(a,str) and isinstance(b,str)
        left,right=support(a),support(b)
        assert not left&right,'a selector block repeats a supplied hat'
        return left|right
    found=[tuple(sorted(support(n))) for n in TERMS]
    assert found==list(SUPPORTS)
    assert sorted(i for g in found for i in g)==list(range(24))
    assert support(SUM)==frozenset(range(24))
    return found


def rewrite_rows(old):
    """Exact local identity; a complete host theorem needs a canonical guard."""
    scale.checked_source(old['source'],old['parameters'],old['auxiliaries'])
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert rows['selector_sum__4']==('+','Shat0','Shat1')
    for i in range(5,27):assert rows[f'selector_sum__{i}']==('+',f'Shat{i-3}',f'selector_sum__{i-1}')
    support_rows(old)
    required={'linear_shared_sum__410':('+','linear_sum__392','linear_sum__409'),
        'linear_constant__411':('-','linear_shared_sum__410',58328),
        'linear_shared_sum__429':('+','linear_sum__392','linear_sum__428'),
        'linear_constant__430':('-','linear_shared_sum__429',58328)}
    assert all(rows.get(n)==v for n,v in required.items())
    consumers={f'selector_sum__{i}':f'selector_sum__{i+1}' for i in range(9,26)}
    consumers.update(linear_shared_sum__410='linear_constant__411',linear_shared_sum__429='linear_constant__430')
    for private,consumer in consumers.items():
        assert {n for n,_,a,b in old['source'] if private in (a,b)}=={consumer},'erased prefix has another consumer'
    for key in PUBLIC_KEYS:assert not DELETED&leaves(old.get(key)),key
    added=[];last=TERMS[0]
    for i,term in enumerate(TERMS[1:]):
        n=SUM if i==len(TERMS)-2 else f'c2_shared_selector_sum_{i}'
        added.append((n,'+',last,term));last=n
    added.append((SHIFT,'-','linear_sum__392',58328))
    assert not ({n for n,_,_,_ in added}-{SUM})&(set(rows)|set(old['parameters']+old['auxiliaries']))
    changes={'linear_constant__411':('+',SHIFT,'linear_sum__409'),
             'linear_constant__430':('+',SHIFT,'linear_sum__428')}
    source=[(n,*changes.get(n,(o,a,b))) for n,o,a,b in old['source'] if n not in DELETED|{SUM}]+added
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    c=Counter(o for _,o,_,_ in source);b=Counter(o for _,o,_,_ in old['source'])
    assert len(source)==len(old['source'])-12 and c['*']==b['*'] and c['+']+c['-']==b['+']+b['-']-12
    return source


def naive_degrees(source,inputs):
    d={n:1 for n in inputs}
    for n,o,a,b in source:
        da=d[a] if isinstance(a,str) else 0;db=d[b] if isinstance(b,str) else 0
        d[n]=da+db if o=='*' else max(da,db)
    return d


def canonical_parent(context,merge_units=True):
    assert context in ('word','universal') and type(merge_units) is bool
    assert context!='word' or merge_units,'word has its single inherited unit product'
    return word.build() if context=='word' else universal.build(merge_units=merge_units)


@lru_cache(None)
def build(context='universal',*,merge_units=True):
    return rewrite(canonical_parent(context,merge_units),context=context,merge_units=merge_units)


def rewrite(old,*,context='universal',merge_units=True):
    assert old==canonical_parent(context,merge_units),'complete canonical C2 parent required'
    source=rewrite_rows(old)
    packet=scale.metadata(dict(old,source=source,c2_selector_sharing=True,
        selector_sharing_parent=old,selector_sharing_context=context,selector_sharing_merge=merge_units,
        selector_sharing_terms=list(TERMS),selector_sharing_supports=[list(g) for g in SUPPORTS],
        selector_sharing_deleted=sorted(DELETED),
        identical_complete_polynomial=True,identical_positive_coordinates=True,
        identical_positive_zero_set=True,positive_zero_bijection=True,
        selector_sharing_scope='Exact all-integer graph identity with the matching literal C2 word374 or universal440/442 parent; no native or loader hypothesis changes.'))
    assert packet['operations']==old['operations']-12
    assert packet['multiplications']==old['multiplications']
    assert packet['additions_subtractions']==old['additions_subtractions']-12
    for key in PUBLIC_KEYS:assert packet.get(key)==old.get(key),key
    a=naive_degrees(source,old['parameters']+old['auxiliaries'])
    b=naive_degrees(old['source'],old['parameters']+old['auxiliaries'])
    assert all(a[n]==v for n,v in b.items() if n not in DELETED)
    return packet


def checked_packet(packet):
    assert packet==build(packet['selector_sharing_context'],merge_units=packet['selector_sharing_merge']),'canonical shared source required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet);old=packet['selector_sharing_parent']
    # The guarded replacements have degree1 and every retained bound agrees.
    # Both literal main-norm cancellation subgraphs are completely untouched.
    return (word.norms.degree_bound(old,sum_of_squares=sum_of_squares) if packet['selector_sharing_context']=='word'
            else universal.degree_bound(old,sum_of_squares=sum_of_squares))


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in source)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],
            output=out,**degree_bound(packet,sum_of_squares=sum_of_squares)))


def restore_registers(env):
    restored={f'selector_sum__{i}':sum(env[f'Shat{j}'] for j in range(i-2)) for i in range(9,26)}
    restored['linear_shared_sum__410']=env['linear_sum__392']+env['linear_sum__409']
    restored['linear_shared_sum__429']=env['linear_sum__392']+env['linear_sum__428']
    return restored


def audit(packet,seed,cases=64):
    old=packet['selector_sharing_parent'];rng=random.Random(seed);totals=Counter()
    old_final=word.polynomial_source if packet['selector_sharing_context']=='word' else universal.polynomial_source
    schedules=[(polynomial_source(packet,sum_of_squares=sos),old_final(old,sum_of_squares=sos)) for sos in (False,True)]
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in packet['parameters']+packet['auxiliaries']}
        if case in (0,cases//2):values.update({f'Shat{i}':1 for i in range(24)});totals['zero_unhatted_selector_assignments']+=1
        a=execute(packet['source'],values);b=execute(old['source'],values)
        assert all(a[n]==v for n,v in b.items() if n not in DELETED)
        restored=restore_registers(a);assert set(restored)==DELETED
        assert all(restored[n]==b[n] for n in DELETED)
        assert a[SUM]==sum(values[f'Shat{i}'] for i in range(24))
        assert a['linear_constant__411']==a['linear_sum__392']+a['linear_sum__409']-58328
        assert a['linear_constant__430']==a['linear_sum__392']+a['linear_sum__428']-58328
        for (ns,no),(os,oo) in schedules:
            assert execute(ns,values)[no]==execute(os,values)[oo]
            totals['complete_output_identities']+=1;totals['signed_output_identities']+=signed
        totals['complete_retained_register_and_manual_restoration_maps']+=1;totals['signed_assignments']+=signed
    return dict(totals)


def guards():
    old=canonical_parent('universal');bad=[]
    bad.append(dict(old,source=old['source']+[('leak','+','selector_sum__12',1)]))
    bad.append(dict(old,interfaces={'nested':[{'prefix':'linear_shared_sum__410'}]}))
    bad.append(dict(old,ordinary_comparisons=[('selector_sum__25',1)]))
    bad.append(dict(old,source=[(n,'-',a,b) if n=='linear_group__374' else (n,o,a,b) for n,o,a,b in old['source']]))
    bad.append(dict(old,source=[(n,o,a,58327) if n=='linear_constant__430' else (n,o,a,b) for n,o,a,b in old['source']]))
    bad.append(dict(old,source=old['source']+[(SHIFT,'+',1,1)]))
    for v in bad:
        try:rewrite_rows(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('malformed local caller accepted')
    for v in (dict(old,comparisons=[]),build()):
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('noncanonical complete caller accepted')
    return len(bad)+2


def verify():
    records=[];totals=Counter()
    for context,merge in (('word',True),('universal',False),('universal',True)):
        packet=build(context,merge_units=merge);old=packet['selector_sharing_parent']
        counts=audit(packet,428120+len(records));totals.update(counts)
        for sos in (False,True):
            ss,out=polynomial_source(packet,sum_of_squares=sos)
            os,oo=(word.polynomial_source(old,sum_of_squares=sos) if context=='word' else universal.polynomial_source(old,sum_of_squares=sos))
            rec=ledger(packet,sum_of_squares=sos);c=Counter(o for _,o,_,_ in os)
            assert len(ss)==len(os)-12 and rec['polynomial']['multiplications']==c['*']
            assert universal.closure(ss,out,packet['parameters']+packet['auxiliaries'])==len(ss)
            rec.update(context=context,merge_units=merge,sum_of_squares=sos,audit=counts,
                source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest())
            records.append(rec)
    assert ledger()['polynomial']['operations']==428
    assert ledger(build('word'))['polynomial']['operations']==362
    return dict(status='PASS_TSEYTIN_SELECTOR_SHARING428',forms=records,audit_totals=dict(totals),
        selector_terms=list(TERMS),selector_supports=[list(g) for g in SUPPORTS],
        erased_private_registers=sorted(DELETED),rejected_callers=guards(),
        scope='Exact full integer polynomial identity relative to literal word374 and universal440/442 parents; same supplied coordinates and propagated degree dictionaries. No new source theorem or unrestricted circuit-optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['audit_totals'])
    print([(r['context'],r['merge_units'],r['sum_of_squares'],r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in result['forms']])
