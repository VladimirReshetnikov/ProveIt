"""Computed truth fields, a factored index and its smaller native bound.

The complete product-scale412 parent has positive implicit fields at its
retained global bound. Fix checksum one, erase three native coordinates
and two port comparisons, then factor the private index. The paid bound
becomes X=q*(S+beta), where r=(q-1)*S. Complete cost401, with62 witnesses.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_product_scale412 as parent

word=parent.word
scale=parent.scale
execute=parent.execute
FIELDS={'and__F0','and__F1','and__F2'}
CHECKSUM='and__bs_q'
PACKED='and__bs_packed'
INNER='and__factored_index_inner'
BOUND='and__bound_beta'
DELETED={'and__input_A','and__input_B','and__shared_sum02','and__bs_Q',CHECKSUM,
         'and__bs_p0','and__bs_p1','and__bs_p2','and__bs_p3','and__bs_p4',
         'and__norm_unit_product2'}
PORT_PAIRS=[('and__input_A','and__padded_A'),('and__input_B','and__padded_B')]
REQUIRED={
    'and__shared_sum02':('+','and__F0','and__F2'),
    'and__input_A':('+','and__F1','and__F3'),
    'and__input_B':('+','and__F2','and__F3'),
    'and__bs_Q':('+','and__shared_sum02','and__input_A'),
    CHECKSUM:('-','and__q','and__bs_Q'),
    'and__bs_p0':('*','and__q','and__F3'),
    'and__bs_p1':('+','and__F2','and__bs_p0'),
    'and__bs_p2':('*','and__q','and__bs_p1'),
    'and__bs_p3':('+','and__F1','and__bs_p2'),
    'and__bs_p4':('*','and__q','and__bs_p3'),
    PACKED:('+','and__F0','and__bs_p4'),
    'and__norm_unit_product2':('*','and__norm_unit_product1',CHECKSUM),
    'and__normalized_norm_units':('*','and__norm_unit_product2','and__f_square_minus_one'),
    'and__padded_A':('+','and__scaled_A',12),
    'and__padded_B':('+','and__scaled_B',10),
    'and__F3':('+','and__scaled_Z',8),
    'and__bs_X_bound':('+',PACKED,BOUND),
    'and__wn2':('*','and__bs_X_bound','and__q')}
NEW_ROWS=[
    ('and__factored_q_minus_one','-','and__q',1),
    ('and__factored_q_plus_one','+','and__q',1),
    ('and__factored_output_product','*','and__factored_q_minus_one','and__F3'),
    ('and__factored_input_sum','+','and__padded_B','and__factored_output_product'),
    ('and__factored_scaled_input','*','and__factored_q_plus_one','and__factored_input_sum'),
    (INNER,'+','and__padded_A','and__factored_scaled_input'),
    (PACKED,'*','and__factored_q_minus_one',INNER)]


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical412 parent required'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows.get(n)==row for n,row in REQUIRED.items()),'literal field/index/bound fragment required'
    for n in FIELDS|DELETED|{'and__padded_A',BOUND}:
        actual={t for t,_,a,b in old['source'] if n in (a,b)}
        expected={t for t,(_,a,b) in REQUIRED.items() if n in (a,b)}
        assert actual==expected,(n,actual,expected)
    assert all(old['comparisons'].count(pair)==1 and old['ordinary_comparisons'].count(pair)==1 for pair in PORT_PAIRS)
    assert old['word_factors'].count(CHECKSUM)==1
    active=('parameters','interfaces','power_factors','word_unit_register','power_unit_register','unit_register')
    for key in active:
        assert not (FIELDS|DELETED|{BOUND,'and__padded_A'})&parent.parent.parent.leaves(old.get(key)),key
    assert not ({n for n,_,_,_ in NEW_ROWS}-{PACKED})&(set(rows)|set(old['parameters']+old['auxiliaries']))
    changes={'and__padded_A':('+','and__scaled_A',13),
             'and__normalized_norm_units':('*','and__norm_unit_product1','and__f_square_minus_one'),
             'and__bs_X_bound':('+',INNER,BOUND)}
    source=[(n,*changes.get(n,(op,a,b))) for n,op,a,b in old['source'] if n not in DELETED|{PACKED}]+NEW_ROWS
    auxiliaries=[n for n in old['auxiliaries'] if n not in FIELDS]
    source=scale.sort_source(source,old['parameters']+auxiliaries)
    scale.checked_source(source,old['parameters'],auxiliaries)
    # Verify independence of the triangular gap change after field erasure.
    lookup={n:(a,b) for n,_,a,b in source};seen=set();todo=[PACKED,INNER]
    while todo:
        n=todo.pop()
        if isinstance(n,str) and n not in seen:
            seen.add(n)
            if n in lookup:todo.extend(lookup[n])
    assert BOUND not in seen and not FIELDS&seen
    p=scale.metadata(dict(old,source=source,auxiliaries=auxiliaries,
        comparisons=[pair for pair in old['comparisons'] if pair not in PORT_PAIRS],
        ordinary_comparisons=[pair for pair in old['ordinary_comparisons'] if pair not in PORT_PAIRS],
        word_factors=[f for f in old['word_factors'] if f!=CHECKSUM],
        computed_fields_parent=old,computed_truth_fields=True,checksum_fixed_one=True,
        factored_native_index=True,native_inner_bound=True,
        interfaces=dict(old['interfaces'],native_index=PACKED,native_index_inner=INNER),
        padded_A_register_meaning='and__padded_A now represents A+1=16H+13; the old port A=16H+12 is restored mathematically.',
        native_bound_coordinate='and__bound_beta is X/q-S, with S=and__factored_index_inner; historical parent helpers require the explicit field/bound lift.',
        native_equivalence='On valid program slices, positive-zero bijection with the checksum-one slice of412; all412 positive zeros normalize to that slice without changing outer data.',
        identical_complete_polynomial=False,identical_positive_coordinates=False,
        identical_positive_zero_set=False,positive_zero_bijection=False,
        checksum_one_slice_bijection=True,positive_zero_bijection_scope='valid program slices',
        integer_polynomial_identity_after_lift=True))
    assert p['operations']==old['operations']-5 and p['witnesses']==old['witnesses']-3
    assert p['multiplications']==old['multiplications']-1 and p['additions_subtractions']==old['additions_subtractions']-4
    assert p['equations']==old['equations']-2
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical computed401 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.degrees_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    deg=degree_dictionary(packet);d=lambda v:deg[v] if isinstance(v,str) else 0
    for n,op,a,b in source:
        if n not in deg:deg[n]=d(a)+d(b) if op=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=deg[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        native_scale_degree=d('and__q'),native_index_degree=d(PACKED),
        native_inner_degree=d(INNER),native_X_degree=d('and__wn2'),
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),
        exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(op for _,op,_,_ in source)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],
                        output=out,**degree_bound(packet,sum_of_squares=sum_of_squares)))


def fields_and_index(env):
    A=16*env['joined_H__287']+12;C=16*env['joined_M__293']+10;Z=16*env['joined_Z__294']+8;q=env['and__q']
    F1=A-Z;F2=C-Z;F0=q-A-C+Z-1
    S=A+1+(q+1)*(C+(q-1)*Z);r=F0+q*F1+q*q*F2+q**3*Z
    assert r==(q-1)*S
    return dict(A=A,C=C,Z=Z,q=q,F0=F0,F1=F1,F2=F2,S=S,r=r)


def lift_to_parent(packet,values):
    env=execute(packet['source'],values);v=fields_and_index(env)
    return dict(values,**{f'and__F{i}':v[f'F{i}'] for i in range(3)},
                **{BOUND:values[BOUND]+v['S']-v['r']})


def project_parent_zero(packet,values):
    """On a parent zero, normalize checksum if needed and erase the fields.

    This formula also defines an integer map off zero, but no output
    identity or positivity there is claimed for this direction.
    """
    old=packet['computed_fields_parent'];env=execute(old['source'],values)
    A=env['and__padded_A'];C=env['and__padded_B'];Z=env['and__F3'];q=env['and__q']
    S=A+1+(q+1)*(C+(q-1)*Z)
    return {n:(values[n]+env[PACKED]-S if n==BOUND else values[n]) for n in packet['parameters']+packet['auxiliaries']}


def source_audit(cases=80):
    counts=Counter();rng=random.Random(401621)
    for merge in (False,True):
        p=build(merge_units=merge);old=p['computed_fields_parent']
        schedules=[(polynomial_source(p,sum_of_squares=s),parent.polynomial_source(old,sum_of_squares=s)) for s in (False,True)]
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%20==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_selector_cases']+=1
            env=execute(p['source'],values);f=fields_and_index(env);lift=lift_to_parent(p,values)
            prior=execute(old['source'],lift)
            assert prior[CHECKSUM]==1 and prior['and__input_A']==f['A'] and prior['and__input_B']==f['C']
            assert prior['and__padded_A']+1==env['and__padded_A']
            assert all(env[n]==prior[n] for n,_,_,_ in old['source'] if n not in DELETED|{'and__padded_A'})
            assert env[INNER]==f['S'] and env[PACKED]==f['r']
            assert project_parent_zero(p,lift)==values
            counts['nonpositive_formal_parent_bound_gaps']+=lift[BOUND]<=0
            counts['nonpositive_formal_truth_field_assignments']+=min(f[f'F{i}'] for i in range(3))<=0
            for (ns,no),(os,oo) in schedules:
                assert execute(ns,values)[no]==execute(os,lift)[oo]
                counts['complete_integer_lift_output_identities']+=1;counts['signed_output_identities']+=signed
            counts['complete_retained_register_maps']+=1;counts['signed_register_maps']+=signed
    return dict(counts)


def scalar_audit():
    counts=Counter();p=build()
    coords=['H_U','H_V']+[f'Z{side}hat{i}' for side in ('U','V') for i in range(4)]
    for D in (1,2,3,8,17):
      for J in (1,2,5):
       for tile in (0,5,8,14,17,23):
        for heavy in (-1,0,2,6,9):
            values={n:1 for n in p['parameters']+p['auxiliaries']}
            values['height_slack']=D;values[f'Shat{tile}']=J+1
            B=65536*D;P=(B-1)*J+1
            if heavy>=0:values[coords[heavy]]=P-10
            values['global_bound']=P-sum(values[n] for n in coords)
            env=execute(p['source'],values);f=fields_and_index(env);T=P**34
            assert env['global_lhs__40']==env['P__30']==P
            H,M,Z=(env[n] for n in ('joined_H__287','joined_M__293','joined_Z__294'))
            assert H-Z>=T+1 and M-Z>=1 and B*T-H-M+Z>=(B-5)*T+2
            assert min(f[f'F{i}'] for i in range(3))>0 and sum(f[f'F{i}'] for i in range(3))+f['Z']==f['q']-1
            assert [f[f'F{i}']%16 for i in range(3)]+[f['Z']%16]==[1,4,2,8]
            assert f['r']>=sum(f['q']**i for i in range(4)) and f['r']<f['q']**4
            assert f['S']>0 and f['r']>f['S'] and env['and__wn2']>f['r']
            # Positive old gap at a typed zero follows without constructing X.
            assert f['q']<f['r'] and 2*f['r']+1>2*f['r'].bit_length()
            counts['positive_pretyping_field_bound_contexts']+=1;counts['height_one_contexts']+=D==1
            counts['nondyadic_scale_contexts']+=f['q']&(f['q']-1)!=0
    return dict(counts,scope='Outer source fixtures satisfying only the retained global bound, not full native Pell zeros.')


def normalization_audit():
    counts=Counter()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['computed_fields_parent']
      for D in (1,2,3):
       for J in (1,2):
        for tile in (0,14):
            values={n:1 for n in p['parameters']+p['auxiliaries']}
            values['height_slack']=D;values[f'Shat{tile}']=J+1
            B=65536*D;P=(B-1)*J+1;values['global_bound']=P-10
            f=fields_and_index(execute(p['source'],values));q,r,S=f['q'],f['r'],f['S']
            values[BOUND]=3+r-S
            X=q*(r+3);Y=3*q;E=X*Y;k=E+r+1;c=k*Y+1
            values['and__eta']=1;values['and__zeta']=k-1
            values['and__o']=2*c-(2*r+1)
            assert min(values.values())>0
            normal=lift_to_parent(p,values)
            assert normal[BOUND]==3 and min(normal.values())>0
            for eps in (1,-1):
                prior=dict(normal)
                prior['and__F0']+=1-eps;prior[BOUND]-=1-eps
                e=execute(old['source'],prior)
                assert e[CHECKSUM]==eps and e['and__index_unit']==eps and e['and__linear_unit']==1
                assert project_parent_zero(p,prior)==values and min(prior.values())>0
                for sos in (False,True):
                    ns,no=polynomial_source(p,sum_of_squares=sos);os,oo=parent.polynomial_source(old,sum_of_squares=sos)
                    assert execute(ns,values)[no]==execute(os,prior)[oo]
                    counts['complete_conditional_normalization_outputs']+=1
                counts['positive_signed_checksum_branch_contexts']+=1
    return dict(counts,scope='Positive structured Qc=Nk=epsilon,Nl=1 fixtures with unrestricted norm residuals; not full Pell zeros.')


def guards():
    old=parent.build();bad=[]
    for n in REQUIRED:
        bad.append(dict(old,source=[(t,op,a,0 if t==n else b) for t,op,a,b in old['source']]))
    bad.extend((dict(old,source=old['source']+[('private_leak','+',BOUND,1)]),
                dict(old,interfaces={'field':'and__F0'}),dict(old,word_factors=[]),
                dict(old,comparisons=[]),dict(old,program_recipe='unrestricted')))
    for packet in bad:
        try:rewrite(packet)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('invalid parent accepted')
    count=len(bad)
    for key,value in [('native_bound_coordinate','old bound'),('checksum_fixed_one',False),
                      ('padded_A_register_meaning','old port'),('auxiliaries',old['auxiliaries'])]:
        for method in (polynomial_source,degree_bound):
            try:method(dict(build(),**{key:value}))
            except (AssertionError,KeyError,TypeError):pass
            else:raise AssertionError('invalid successor accepted')
            count+=1
    return count


def verify():
    import sympy as sp
    q,A,C,Z=sp.symbols('q A C Z');F0=q-A-C+Z-1;F1=A-Z;F2=C-Z
    assert sp.expand(F0+q*F1+q*q*F2+q**3*Z-(q-1)*(A+1+(q+1)*(C+(q-1)*Z)))==0
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);rows,out=polynomial_source(p,sum_of_squares=sos);rec=ledger(p,sum_of_squares=sos)
        assert len(rows)==(401 if merge else 403) and p['witnesses']==62
        assert rec['polynomial']['multiplications']==188
        assert p['operations']==(387 if merge else 386) and p['equations']==(5 if merge else 6)
        parent.base.baseline.closure(rows,out,p['parameters']+p['auxiliaries'])
        rec.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    assert [r['polynomial']['degree_upper_bound'] for r in records]==[4752,9288,4712,9396]
    assert all(r['polynomial']['word_factor_degree_bounds']==[760,1804,416,974,345,345] for r in records)
    return dict(status='PASS_TSEYTIN_COMPUTED_FIELDS401',forms=records,source_replay=source_audit(),
        scalar=scalar_audit(),normalization=normalization_audit(),symbolic_packing_identity=True,rejected_callers=guards(),
        scope='On valid program slices, positive-zero bijection with the checksum-one slice of412 via the exact polynomial field/gap lift; negative-checksum normalization preserves all outer data. Full valid-program universality,62 positive witnesses. No arbitrary positive inverse or full giant Pell-zero fixture claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_replay']);print(result['scalar'])
    print([r['polynomial'] for r in result['forms']])
