"""Reuse two paid selector sums in the C2 affine updates, saving two M.

316*a+317*b=317*(a+b)-a. Both sums are already paid by the
physical selector classes. Complete polynomial and supplied domains
are identical to401, on every integer assignment.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_computed_fields401 as parent

base=parent.parent.base
scale=parent.scale
execute=parent.execute
ALIASES={'linear_sum__406':'linear_sum__405','linear_sum__425':'linear_sum__424'}
CHANGES={
 'linear_coefficient__397':('-','linear_coefficient__398','Shat14'),
 'linear_coefficient__398':('*',317,'group_sum__221'),
 'linear_coefficient__416':('-','linear_coefficient__417','Shat15'),
 'linear_coefficient__417':('*',317,'group_sum__228')}
EXPECTED={
 'linear_coefficient__397':('*','Shat14',316),
 'linear_coefficient__398':('*','Shat16',317),
 'linear_coefficient__416':('*','Shat15',316),
 'linear_coefficient__417':('*','Shat17',317),
 'group_sum__221':('+','Shat14','Shat16'),
 'group_sum__228':('+','Shat15','Shat17'),
 'linear_sum__405':('+','linear_coefficient__397','linear_sum__404'),
 'linear_sum__406':('+','linear_coefficient__398','linear_sum__405'),
 'linear_sum__424':('+','linear_coefficient__416','linear_sum__423'),
 'linear_sum__425':('+','linear_coefficient__417','linear_sum__424')}


def rewrite(old):
    merge=old['merge_units']
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical401 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert all(rows.get(n)==v for n,v in EXPECTED.items())
    consumers={'linear_coefficient__397':{'linear_sum__405'},
        'linear_coefficient__398':{'linear_sum__406'},
        'linear_coefficient__416':{'linear_sum__424'},
        'linear_coefficient__417':{'linear_sum__425'},
        'linear_sum__405':{'linear_sum__406'},'linear_sum__406':{'linear_sum__407'},
        'linear_sum__424':{'linear_sum__425'},'linear_sum__425':{'linear_sum__426'}}
    for n,expected in consumers.items():
        assert {r for r,_,a,b in old['source'] if n in (a,b)}==expected
    source=[(n,*CHANGES[n]) if n in CHANGES else
        (n,o,ALIASES.get(a,a),ALIASES.get(b,b))
        for n,o,a,b in old['source'] if n not in ALIASES]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=source,adjacent_coefficient_parent=old,
        adjacent_coefficient_sharing=True,
        coefficient_equivalence='Exact complete polynomial identity with401 on identical supplied integer coordinates; every domain and interface unchanged.',
        coefficient_comparison_parent='tseytin_computed_fields401',
        coefficient_positive_zero_bijection=True))
    assert p['operations']==old['operations']-2 and p['multiplications']==old['multiplications']-2
    assert p['additions_subtractions']==old['additions_subtractions']
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical coefficient-sharing399 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    old=parent.degree_dictionary(packet['adjacent_coefficient_parent'])
    assert all(old[n]==1 for n in set(EXPECTED)|set(CHANGES))
    return {n:d for n,d in old.items() if n not in ALIASES}


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.degree_bound(packet['adjacent_coefficient_parent'],sum_of_squares=sum_of_squares)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    src,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    counts=Counter(o for _,o,_,_ in src)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(src),multiplications=counts['*'],
            additions_subtractions=counts['+']+counts['-'],output=out,
            **degree_bound(packet,sum_of_squares=sum_of_squares)))


def identity_audit(cases=96):
    rng=random.Random(399401);counts=Counter()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['adjacent_coefficient_parent']
      for i in range(cases):
        signed=i>=cases//2
        draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
        values={n:draw() for n in p['parameters']+p['auxiliaries']}
        if i%16==0:
            values.update({f'Shat{j}':1 for j in range(24)})
            counts['zero_selector_contexts']+=1
        a=execute(old['source'],values);b=execute(p['source'],values)
        changed=set(CHANGES)|set(ALIASES.values())
        assert all(a[n]==b[n] for n,_,_,_ in p['source'] if n not in changed)
        for n,left,right in [('linear_coefficient__397','Shat14','Shat16'),('linear_coefficient__416','Shat15','Shat17')]:
            assert b[n]==316*values[left]+317*values[right]
        assert b['linear_sum__405']==a['linear_sum__406']
        assert b['linear_sum__424']==a['linear_sum__425']
        for sos in (False,True):
            ns,no=polynomial_source(p,sum_of_squares=sos)
            os,oo=parent.polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_polynomial_identities']+=1
            counts['signed_output_identities']+=signed
      before=parent.degree_dictionary(old);after=degree_dictionary(p)
      assert all(after[n]==d for n,d in before.items() if n not in ALIASES)
      counts['retained_degree_dictionary_identities']+=1
    return dict(counts)


def guards():
    old=parent.build();bad=[dict(old,source=old['source'][:-1]),dict(old,interfaces={}),
        dict(old,comparisons=[]),dict(old,program_recipe='unrestricted')]
    for name in EXPECTED:
        bad.append(dict(old,source=[(n,o,a,7 if n==name else b) for n,o,a,b in old['source']]))
    bad.append(dict(old,source=old['source']+[('leaked_coefficient','+','linear_coefficient__397',1)]))
    for candidate in bad:
        try:rewrite(candidate)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated parent accepted')
    total=len(bad)
    for field,value in [('coefficient_positive_zero_bijection',False),('source',build()['source'][:-1]),('interfaces',{})]:
      for call in (polynomial_source,degree_bound,degree_dictionary):
        try:call(dict(build(),**{field:value}))
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated successor accepted')
        total+=1
    return total


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);src,out=polynomial_source(p,sum_of_squares=sos)
        rec=ledger(p,sum_of_squares=sos)
        assert len(src)==(399 if merge else 401) and rec['polynomial']['multiplications']==186
        assert p['witnesses']==62 and p['equations']==(5 if merge else 6)
        base.baseline.closure(src,out,p['parameters']+p['auxiliaries'])
        rec.update(merge_units=merge,sum_of_squares=sos,source=src,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(src,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_ADJACENT_COEFFICIENTS399',forms=records,
        identities=identity_audit(),rejected_callers=guards(),
        scope='Exact all-integer polynomial identity with401 on the same supplied coordinates. Counts include every fixed-coefficient gate; complete universality inherited unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['identities']);print([r['polynomial'] for r in result['forms']])
