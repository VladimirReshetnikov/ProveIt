"""Reuse paid copy-selector prefixes:395 complete universal operations.

h0+2*h1+...+6*h5=6*S5-S4-S3-S2-S1-h0, where Sj=sum(h0..hj).
All prefixes are already paid. Four fixed-numeral multiplications vanish;
the complete integer polynomial, supplied domains and degrees are unchanged.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_adjacent_coefficients399 as parent

scale=parent.scale
execute=parent.execute
DELETED={f'linear0_coefficient__{i}' for i in range(46,50)}
CHANGED={'linear0_coefficient__50':('*',6,'selector_sum__8'),
    'linear_sum__380':('-','linear0_coefficient__50','selector_sum__7'),
    'linear_sum__381':('-','linear_sum__380','selector_sum__6'),
    'linear_sum__382':('-','linear_sum__381','selector_sum__5'),
    'linear_sum__383':('-','linear_sum__382','selector_sum__4'),
    'linear_sum__384':('-','linear_sum__383','Shat0')}
REQUIRED={'selector_sum__4':('+','Shat0','Shat1'),
    **{f'selector_sum__{i}':('+',f'Shat{i-3}',f'selector_sum__{i-1}') for i in range(5,9)},
    **{f'linear0_coefficient__{i+45}':('*',f'Shat{i}',i+1) for i in range(1,6)},
    'linear_sum__380':('+','Shat0','linear0_coefficient__46'),
    **{f'linear_sum__{i}':('+',f'linear0_coefficient__{i-334}',f'linear_sum__{i-1}') for i in range(381,385)}}


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical399 parent required'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows.get(n)==row for n,row in REQUIRED.items()),'literal copy prefixes and weighted sum required'
    consumers={f'linear0_coefficient__{i}':{f'linear_sum__{i+334}'} for i in range(46,51)}
    consumers.update({f'linear_sum__{i}':{f'linear_sum__{i+1}'} for i in range(380,384)})
    for n,expected in consumers.items():
        assert {r for r,_,a,b in old['source'] if n in (a,b)}==expected,'changed private value has another consumer'
    source=[(n,*CHANGED.get(n,(op,a,b))) for n,op,a,b in old['source'] if n not in DELETED]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=source,copy_prefix_parent=old,copy_prefix_sharing=True,
        copy_prefix_identity='sum((i+1)*h[i] for i in range(6))=6*sum(h)-sum(sum(h[:j+1]) for j in range(5))',
        copy_prefix_equivalence='Exact complete polynomial identity with399 on identical supplied integer coordinates, unchanged positive domains and valid program interpretation.',
        copy_prefix_positive_zero_bijection=True))
    assert p['operations']==old['operations']-4 and p['multiplications']==old['multiplications']-4
    assert p['additions_subtractions']==old['additions_subtractions']
    for key in ('parameters','auxiliaries','comparisons','ordinary_comparisons','interfaces','program_recipe','projection'):
        assert p[key]==old[key],key
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical copy-prefix395 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.parent.word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    # Each changed expression is a nonzero degree-one linear form. The
    # unchanged output of this fragment feeds both old norm identities.
    old=parent.degree_dictionary(packet['copy_prefix_parent'])
    assert all(old[n]==1 for n in set(REQUIRED)|set(CHANGED))
    return {n:d for n,d in old.items() if n not in DELETED}


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.degree_bound(packet['copy_prefix_parent'],sum_of_squares=sum_of_squares)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    c=Counter(op for _,op,_,_ in source)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],
            output=out,**degree_bound(packet,sum_of_squares=sum_of_squares)))


def restore_registers(values):
    h=[values[f'Shat{i}'] for i in range(6)]
    restored={f'linear0_coefficient__{i+45}':(i+1)*h[i] for i in range(1,6)}
    restored.update({f'linear_sum__{i+379}':sum((j+1)*h[j] for j in range(i+1)) for i in range(1,5)})
    return restored


def assignment_audit(cases=96):
    rng=random.Random(395397);counts=Counter()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['copy_prefix_parent']
      for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-4,5) if signed else rng.randrange(1,6)
        values={n:draw() for n in p['parameters']+p['auxiliaries']}
        if case%16==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_selector_contexts']+=1
        now=execute(p['source'],values);previous=execute(old['source'],values)
        changed=set(CHANGED)-{'linear_sum__384'}
        assert all(now[n]==v for n,v in previous.items() if n not in DELETED|changed)
        restored=restore_registers(values)
        assert set(restored)==DELETED|changed and all(restored[n]==previous[n] for n in restored)
        assert now['linear_sum__384']==sum((i+1)*values[f'Shat{i}'] for i in range(6))
        for sos in (False,True):
            ns,no=polynomial_source(p,sum_of_squares=sos);os,oo=parent.polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_output_identities']+=1;counts['signed_output_identities']+=signed
        counts['complete_retained_register_and_restoration_maps']+=1;counts['signed_register_maps']+=signed
    return dict(counts)


def guards():
    old=parent.build();bad=[]
    for n in REQUIRED:
        bad.append(dict(old,source=[(r,op,a,0 if r==n else b) for r,op,a,b in old['source']]))
    for n in DELETED|(set(CHANGED)-{'linear_sum__384'}):
        bad.append(dict(old,source=old['source']+[('extra_private_consumer','+',n,1)]))
        bad.append(dict(old,interfaces=dict(old['interfaces'],nested={n:[n]})))
    bad.extend((dict(old,comparisons=[]),dict(old,program_recipe='unrestricted')))
    for candidate in bad:
        try:rewrite(candidate)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('mutated canonical parent accepted')
    count=len(bad)
    for key,value in [('copy_prefix_positive_zero_bijection',False),('source',build()['source'][:-1]),('interfaces',{})]:
      for api in (polynomial_source,degree_bound,degree_dictionary):
        try:api(dict(build(),**{key:value}))
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('mutated successor accepted')
        count+=1
    return count


def verify():
    # Exact coefficient-vector expansion of the discrete prefix identity.
    vector=[6]*6
    for j in range(5):
        for i in range(j+1):vector[i]-=1
    assert vector==list(range(1,7))
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);rows,out=polynomial_source(p,sum_of_squares=sos)
        rec=ledger(p,sum_of_squares=sos);old=p['copy_prefix_parent']
        assert len(rows)==(395 if merge else 397) and rec['polynomial']['multiplications']==182
        assert p['operations']==(381 if merge else 380) and p['witnesses']==62 and p['equations']==(5 if merge else 6)
        parent.base.baseline.closure(rows,out,p['parameters']+p['auxiliaries'])
        before=parent.degree_dictionary(old);after=degree_dictionary(p)
        assert all(after[n]==d for n,d in before.items() if n not in DELETED)
        rec.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_COPY_PREFIX395',forms=records,
        exact_weight_vector=vector,source_replay=assignment_audit(),rejected_callers=guards(),
        scope='Exact complete integer polynomial identity with canonical399 on the same supplied coordinates and program/input domains. Four fewer fixed-numeral multiplications; no global schedule optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_replay'])
    print([r['polynomial'] for r in result['forms']])
