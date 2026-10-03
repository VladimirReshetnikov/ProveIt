"""Reuse B*P^34 as the native scale in the complete free-height C2 compiler.

The top tags become2 and1. Positive q=16*B*P^34 types B and P
before lane splitting; three private power gates disappear. Acceptance
is preserved by fresh positive native extensions, not an off-zero identity.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_free_height415 as parent
import tseytin_universal_factor_partitions as degrees_helper

base=parent.base
word=parent.word
scale=parent.scale
execute=parent.execute
DELETED={'P9__295','P18__296','P36__297'}
CHANGED={
    'top_mask__290':('*',2,'P34__284'),
    'joined_H__287':('+','joined_H__286','top_mask__290'),
    'joined_M__293':('+','joined_M__292','P34__284'),
    'and__q':('*',16,'top_history__285')}
OLD_ROWS={
    'P9__295':('*','P8__277','P__30'),
    'P18__296':('*','P9__295','P9__295'),
    'P36__297':('*','P18__296','P18__296'),
    'top_history__285':('*','B__3','P34__284'),
    'top_mask__290':('*','Bm1__28','P34__284'),
    'joined_H__287':('+','joined_H__286','top_history__285'),
    'joined_M__293':('+','joined_M__292','top_mask__290'),
    'and__q':('*',16,'P36__297')}


def rewrite(old):
    merge=old['merge_units']
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical415 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert all(rows.get(n)==v for n,v in OLD_ROWS.items())
    for n,consumers in [('P9__295',{'P18__296'}),('P18__296',{'P36__297'}),('P36__297',{'and__q'})]:
        assert {r for r,_,a,b in old['source'] if n in (a,b)}==consumers
    source=[(n,*CHANGED.get(n,(o,a,b))) for n,o,a,b in old['source'] if n not in DELETED]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    p=scale.metadata(dict(old,source=source,product_scale_parent=old,
        product_history_scale=True,
        interfaces=dict(old['interfaces'],native_high_scale='top_history__285',
            history_top_scale='P34__284',native_top_tags=[2,1]),
        identical_complete_polynomial=False,identical_positive_coordinates=False,
        identical_positive_zero_set=False,positive_zero_bijection=False,
        height_equivalence='The affine height map is historical415-to418 provenance; the current product-scale transfer rebuilds private native witnesses.',
        native_equivalence='Same accepted ordinary inputs on valid program slices, rebuilding private native witnesses.'))
    assert p['operations']==old['operations']-3
    assert p['multiplications']==old['multiplications']-3
    assert p['additions_subtractions']==old['additions_subtractions']
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(p):
    assert p==build(merge_units=p['merge_units']),'complete canonical product-scale412 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    # The helper checks the two literal norm cancellation graphs. This
    # caller supplies its own stricter whole-packet source/domain guard.
    return degrees_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet)
    d=lambda v:degrees[v] if isinstance(v,str) else 0
    for n,o,a,b in source:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],
        word_factor_degree_bounds=[d(f) for f in packet['word_factors']],
        power_factor_degrees=[d(f) for f in packet['power_factors']],
        native_scale_degree=d('and__q'),history_top_scale_degree=d('P34__284'),
        exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    c=Counter(o for _,o,_,_ in source)
    return dict(certificate={k:packet[k] for k in
        ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],
            additions_subtractions=c['+']+c['-'],output=out,
            **degree_bound(packet,sum_of_squares=sum_of_squares)))


def overridden_parent(source,values):
    """Independent scalar port replay, explicitly not the old polynomial."""
    env=dict(values)
    get=lambda v:env[v] if isinstance(v,str) else v
    for n,o,a,b in source:
        if n=='top_mask__290':v=2*env['P34__284']
        elif n=='joined_H__287':v=env['joined_H__286']+2*env['P34__284']
        elif n=='joined_M__293':v=env['joined_M__292']+env['P34__284']
        elif n=='and__q':v=16*env['B__3']*env['P34__284']
        else:
            u,v=get(a),get(b)
            v=u*v if o=='*' else u+v if o=='+' else u-v
        env[n]=v
    return env


def source_audit(cases=80):
    rng=random.Random(412414);counts=Counter()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['product_scale_parent']
      for case in range(cases):
        signed=case>=cases//2
        draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,4)
        values={n:draw() for n in p['parameters']+p['auxiliaries']}
        if case%20==0:
            values.update({f'Shat{i}':1 for i in range(24)})
            counts['zero_selector_contexts']+=1
        new=execute(p['source'],values);prior=overridden_parent(old['source'],values)
        assert all(new[n]==prior[n] for n,_,_,_ in p['source'])
        for sos in (False,True):
            src,out=polynomial_source(p,sum_of_squares=sos)
            os,oo=parent.polynomial_source(old,sum_of_squares=sos)
            assert execute(src,values)[out]==overridden_parent(os,values)[oo]
            counts['complete_overridden_output_identities']+=1
            counts['signed_output_identities']+=signed
    return dict(counts)


def scalar_audit():
    counts=Counter();p=build()
    for D in (1,2,3,4,8):
      for J in (1,2,5,11):
       for tile in (0,5,8,14,17,23):
        values={n:1 for n in p['parameters']+p['auxiliaries']}
        values['height_slack']=D;values[f'Shat{tile}']=J+1
        B=65536*D;P=(B-1)*J+1;values['global_bound']=P-10
        env=execute(p['source'],values);T=P**34;Q=B*T
        assert env['global_lhs__40']==env['P__30']==P and B<=P
        H0,M0,Z=(env[n] for n in ('joined_H__286','joined_M__292','joined_Z__294'))
        assert all(0<=v<T for v in (H0,M0,Z))
        H,M=H0+2*T,M0+T
        assert env['and__q']==16*Q and env['joined_H__287']==H and env['joined_M__293']==M
        assert H-Z>=T+1 and M-Z>=1 and Q-H-M+Z>=(B-5)*T+2
        assert max(H,M,Z)<Q
        counts['positive_global_contexts']+=1;counts['height_one_contexts']+=D==1
    # Independent scalar extremes, including nonpowers before typing.
    for B in (8,16,17,32,65536):
      for T in (1,2,3,4,8,17):
       for H0 in (0,T-1):
        for M0 in (0,T-1):
         for Z in (0,T-1):
          H,M,Q=H0+2*T,M0+T,B*T
          assert H-Z>=T+1 and M-Z>=1 and Q-H-M+Z>=(B-5)*T+2
          assert max(H,M,Z)<Q
          counts['untyped_extreme_port_bounds']+=1
    for T in (1,2,4,8,16):
      for H0 in range(T):
       for M0 in range(T):
        assert ((H0+2*T)&(M0+T))==H0&M0
        counts['binary_top_split_cases']+=1
    return dict(counts,scope='Exact source/scalar fixtures, not full native Pell zeros.')


def guards():
    old=parent.build();bad=[dict(old,source=old['source'][:-1]),
        dict(old,interfaces={}),dict(old,comparisons=[]),dict(old,auxiliaries=old['auxiliaries'][:-1]),
        dict(old,program_recipe='unrestricted')]
    for n in OLD_ROWS:
        rows=[(r,o,a,7 if r==n else b) for r,o,a,b in old['source']]
        bad.append(dict(old,source=rows))
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated parent accepted')
    n=len(bad)
    for k,v in [('positive_zero_bijection',True),('source',build()['source'][:-1]),('interfaces',{})]:
      for method in (polynomial_source,degree_bound):
        try:method(dict(build(),**{k:v}))
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated successor accepted')
        n+=1
    return n


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);src,out=polynomial_source(p,sum_of_squares=sos)
        rec=ledger(p,sum_of_squares=sos)
        assert len(src)==(412 if merge else 414)
        assert rec['polynomial']['multiplications']==191 and p['witnesses']==65
        assert rec['polynomial']['native_scale_degree']==69
        base.baseline.closure(src,out,p['parameters']+p['auxiliaries'])
        rec.update(merge_units=merge,sum_of_squares=sos,source=src,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(src,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_PRODUCT_SCALE412',forms=records,source_replay=source_audit(),
        scalar=scalar_audit(),rejected_callers=guards(),
        scope='Complete valid-program acceptance equivalence via fresh positive native extensions. Modified-port source replay is not an arbitrary-point equality of the old and new polynomials.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_replay']);print(result['scalar'])
    print([r['polynomial'] for r in result['forms']])
