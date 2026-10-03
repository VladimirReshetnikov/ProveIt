"""Two local checksum signs and a global unit: complete U15,2 774 ->771.

Checksum-only772 has the same full supplied positive zeros. The global
unit variant has the positive affine bijection beta_parent=beta_new+1.
Neither change is an off-zero polynomial identity. Both initial interfaces
and their literal finalizers remain fully charged.
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

import gpcp_shared_selectors774 as parent

CHECKSUM='hist__and__bs_q'
GLOBAL_PAIR=('hist__global_lhs__73','hist__P__63')
GLOBAL='history_global_unit'
CHECKSUM_PRODUCT='both_checksum_units'
TOTAL='checksum_global_units'
BETA='hist__global_bound'
PORTS=['hist__H_U','hist__H_V']+[f'hist__Z{side}hat{i}' for side in ('U','V') for i in range(4)]


def source_contract(old):
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(rows)==len(old['source'])
    assert old['unit_product'] and old['regroup']
    assert len(old['unit_factors'])==13 and old['unit_factors'].count('and__bs_q')==1
    assert CHECKSUM not in old['unit_factors']
    assert old['comparisons'][-1]==(old['unit_register'],1)
    assert old['comparisons'].count((CHECKSUM,1))==1 and old['comparisons'].count(GLOBAL_PAIR)==1
    assert rows['hist__J__60']==('-','hist__selector_sum__59',57)
    assert rows['hist__B__3']==('*','hist__height_sum__2',131072)
    assert rows['hist__Bm1__61']==('-','hist__B__3',1)
    assert rows['hist__P_product__62']==('*','hist__Bm1__61','hist__J__60')
    assert rows['hist__P__63']==('+','hist__P_product__62',1)
    assert rows[GLOBAL_PAIR[0]]==('+',BETA,'hist__global_sum__72')
    assert {n for n,_,a,b in old['source'] if BETA in (a,b)}=={GLOBAL_PAIR[0]}
    assert not any(BETA in pair for pair in old['comparisons'])
    for prefix in ('and__','hist__and__'):
        expected={
            'bs_q':('-',prefix+'q',prefix+'bs_Q'),
            'bs_Q':('+',prefix+'shared_sum02',prefix+'input_A'),
            'shared_sum02':('+',prefix+'F0',prefix+'F2'),
            'input_A':('+',prefix+'F1',prefix+'F3'),
            'input_B':('+',prefix+'F2',prefix+'F3'),
            'padded_A':('+',prefix+'scaled_A',12),
            'padded_B':('+',prefix+'scaled_B',10),
            'F3':('-' if prefix=='and__' else '+',prefix+'scaled_Z',8),
            'wn2':('*',prefix+'w',prefix+'q'),
            'sn2':('*',prefix+'bs_odd',prefix+'q'),
            'bs_odd':('+',prefix+'bs_even',1),
            'bs_even':('*',2,prefix+'odd_half'),
            'bs_X_bound':('+',prefix+'bs_packed',prefix+'bound_beta')}
        assert all(rows[prefix+n]==v for n,v in expected.items())
        for a,b in [('input_A','padded_A'),('input_B','padded_B'),('R10b','R11'),
                    ('H17','aux_u_rhs'),('bs_X_bound','wn2')]:
            assert (prefix+a,prefix+b) in old['comparisons']
        assert all(prefix+n in old['auxiliaries'] for n in ('F0','F1','F2','bound_beta'))
    assert all(n not in rows for n in (GLOBAL,CHECKSUM_PRODUCT,TOTAL))


def rewrite(old,*,global_unit=True):
    inline=old.get('inline_initial')
    assert type(inline)is bool and type(global_unit)is bool
    assert old==parent.build(inline_initial=inline),'complete canonical shared-selector774 parent required'
    source_contract(old)
    rows=list(old['source'])+[(CHECKSUM_PRODUCT,'*',old['unit_register'],CHECKSUM)]
    pairs=[pair for pair in old['comparisons'][:-1] if pair!=(CHECKSUM,1)]
    factors=list(old['unit_factors'])+[CHECKSUM];unit=CHECKSUM_PRODUCT
    if global_unit:
        rows.extend([(GLOBAL,'-',GLOBAL_PAIR[1],GLOBAL_PAIR[0]),(TOTAL,'*',CHECKSUM_PRODUCT,GLOBAL)])
        pairs.remove(GLOBAL_PAIR);factors.append(GLOBAL);unit=TOTAL
    pairs.append((unit,1))
    p=deepcopy(old)
    counts=Counter(o for _,o,_,_ in rows)
    p.update(source=rows,comparisons=pairs,unit_register=unit,unit_factors=factors,
        operations=len(rows),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],
        equations=len(pairs),checksum_global_parent=old,checksum_signs_proved_locally=True,
        history_checksum_merged=True,history_global_unit=global_unit,
        identical_complete_integer_polynomial=False,identical_positive_zero_set=not global_unit,
        positive_zero_bijection=('hist__global_bound_parent=hist__global_bound_new+1; all other coordinates retained'
                                if global_unit else 'identity on all supplied positive coordinates'),
        projection=('Full supplied positive-zero bijection with774 by the positive global-slack shift; '
                    if global_unit else 'Full supplied positive-zero equality with774; ')+
                   'the two native checksum signs are proved before history or global typing. Program and input data are unchanged.')
    assert p['operations']==old['operations']+(3 if global_unit else 1)
    assert p['equations']==old['equations']-(2 if global_unit else 1)
    return p


@lru_cache(None)
def _build(inline_initial,global_unit):
    return rewrite(parent.build(inline_initial=inline_initial),global_unit=global_unit)


def build(*,inline_initial=True,global_unit=True):
    assert type(inline_initial)is bool and type(global_unit)is bool
    return _build(inline_initial,global_unit)


def checked(packet):
    assert type(packet.get('inline_initial'))is bool and type(packet.get('history_global_unit'))is bool
    assert packet==build(inline_initial=packet['inline_initial'],global_unit=packet['history_global_unit']),\
        'complete canonical checksum/global unit packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet)
    return parent.parent.polynomial_source(packet)


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.raw_degrees(packet)


def degree_audit(packet=None):
    """Exact degree by unchanged old leading forms and two strict new leaders."""
    if packet is None:packet=build()
    checked(packet);old=packet['checksum_global_parent'];prior=parent.degree_audit(old)
    degrees=degree_dictionary(packet);before=parent.degree_dictionary(old)
    assert all(degrees[n]==d for n,d in before.items())
    d=lambda n:degrees[n] if isinstance(n,str) else 0
    nu=d('hist__P__63');qdegree=d('hist__and__q')
    # New checksum highest form is q*: every subtracted field is lower degree.
    assert qdegree>max(d('hist__and__'+n) for n in ('F0','F1','F2','F3'))
    assert d(CHECKSUM)==qdegree
    # New global unit highest form is P*: ten ports and beta all have degree1.
    if packet['history_global_unit']:
        assert nu>max(d(n) for n in PORTS+[BETA]) and d(GLOBAL)==nu
    removed={(CHECKSUM,1)}|({GLOBAL_PAIR} if packet['history_global_unit'] else set())
    assert all(max(d(a),d(b))<prior['maximum_outer_degree'] for a,b in removed)
    maximum=[(a,b,max(d(a),d(b))) for a,b in packet['comparisons'][:-1]
             if max(d(a),d(b))==prior['maximum_outer_degree']]
    assert [list(v) for v in maximum]==prior['maximum_outer_residuals']
    added=qdegree+(nu if packet['history_global_unit'] else 0)
    assert d(packet['unit_register'])==prior['unit_degree']+added
    rows,out=polynomial_source(packet)
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    exact=prior['exact_degree']+added
    assert degrees[out]==exact
    return dict(exact_degree=exact,parent_exact_degree=prior['exact_degree'],
        parent_leading_sha256=prior['leading_sha256'],
        unit_degree=prior['unit_degree']+added,maximum_outer_degree=prior['maximum_outer_degree'],
        factor_degrees={n:d(n) for n in packet['unit_factors']},
        maximum_outer_residuals=[list(v) for v in maximum],
        new_checksum_leading_form='hist__and__q highest homogeneous part',
        global_leading_form='hist__P__63 highest homogeneous part' if packet['history_global_unit'] else None,
        degree_increment=added,all_three_main_norm_cancellations_checked=True,
        exactness_reason='The unchanged nonzero parent unit and maximal sum-of-squares leading forms are multiplied by the nonzero new q leading form, and by the nonzero P leading form when global merging is enabled.')


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);counts=Counter(o for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=counts['*'],
                        additions_subtractions=counts['+']+counts['-'],output=out),
        degree=degree_audit(packet),parameters=packet['parameters'])


def to_parent_values(values,*,global_unit=True):
    assert type(global_unit)is bool
    result=dict(values)
    if global_unit:result[BETA]+=1
    return result


def from_parent_values(values,*,global_unit=True):
    """Formal integer map; positivity of subtraction is a zero-set theorem."""
    assert type(global_unit)is bool
    result=dict(values)
    if global_unit:result[BETA]-=1
    return result


def execute(rows,values):
    e=dict(values)
    for n,o,a,b in rows:
        assert n not in e
        a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
        e[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return e


def source_audit(cases=24):
    rng=random.Random(771772);counts=Counter()
    for inline in (False,True):
      for global_unit in (False,True):
        p=build(inline_initial=inline,global_unit=global_unit);old=p['checksum_global_parent']
        rows,out=polynomial_source(p);previous,target=parent.polynomial_source(old)
        for case in range(cases):
            signed=case>=cases//2
            values={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in p['parameters']+p['auxiliaries']}
            if case%8==0:
                values.update({f'hist__Shat{i}':1 for i in range(57)});counts['zero_decoded_selector_cases']+=1
            e=execute(rows,values);oldvalues=to_parent_values(values,global_unit=global_unit)
            before=execute(previous,oldvalues)
            assert from_parent_values(oldvalues,global_unit=global_unit)==values
            for n,_,_,_ in old['source']:
                if global_unit and n==GLOBAL_PAIR[0]:assert before[n]==e[n]+1
                else:assert before[n]==e[n]
            W=prod(e[n] for n in old['unit_factors']);C=e[CHECKSUM]
            at=lambda n:e[n] if isinstance(n,str) else n
            S=sum((at(a)-at(b))**2 for a,b in p['comparisons'][:-1])
            if global_unit:
                G=e[GLOBAL]
                manual=W*C*G*(1+S)-1
                prior=W*(1+S+(C-1)**2+(G-1)**2)-1
                difference=W*((C*G-1)*(1+S)-(C-1)**2-(G-1)**2)
            else:
                manual=W*C*(1+S)-1;prior=W*(1+S+(C-1)**2)-1
                difference=W*(C-1)*(S-C+2)
            assert e[out]==manual and before[target]==prior and e[out]-before[target]==difference
            counts['complete_retained_register_maps']+=1;counts['signed_maps']+=signed
            counts['complete_parent_manual_output_corrections']+=1
    return dict(counts)


def sign_audit():
    counts=Counter();rng=random.Random(77116)
    # All compositions up to q512, followed by larger independent samples.
    for t in range(4,17):
        q=1<<t;Q=q//16
        if t<=9:
            vectors=((a,b,c,Q-1-a-b-c) for a in range(Q) for b in range(Q-a) for c in range(Q-a-b))
        else:
            vectors=[]
            for _ in range(64):
                cuts=sorted([0,Q-1]+[rng.randrange(Q) for _ in range(3)])
                vectors.append(tuple(cuts[i+1]-cuts[i] for i in range(4)))
        for high in vectors:
            fields=[16*a+b for a,b in zip(high,(3,4,2,8))]
            assert sum(fields)==q+1 and all(0<f<q for f in fields)
            r=sum(f*q**i for i,f in enumerate(fields))
            assert r>q and r>=9 and r.bit_count()==sum(a.bit_count() for a in high)+5
            assert r.bit_count()>t and r.bit_count()>=(Q-1).bit_count()+5==t+1
            counts['negative_checksum_population_cases']+=1
    return dict(counts,scope='Exhaustive high-field compositions for q16 through512; larger sampled dyadic scales. These are component obstructions, not Pell zeros.')


def positive_cone_audit():
    rng=random.Random(771013);counts=Counter()
    for inline in (False,True):
        p=build(inline_initial=inline);by={n:(o,a,b) for n,o,a,b in p['source']}
        roots=['hist__P__63','hist__and__F3','and__F3','and__q','hist__and__q',GLOBAL]
        need=set();todo=list(roots)
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in by and n not in need:
                need.add(n);todo.extend(by[n][1:])
        cone=[r for r in p['source'] if r[0] in need]
        for case in range(80):
            values={n:rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
            if case<8:values.update({f'hist__Shat{i}':1 for i in range(57)})
            e=execute(cone,values)
            assert e['hist__P__63']>=1 and e['hist__and__F3']>=8 and e['and__F3']>=8
            assert e['and__q']>=16 and e['hist__and__q']>=16
            counts['unconditional_computed_port_contexts']+=1
            counts['zero_history_duration_contexts']+=case<8
        # Force the weak negative-global endpoint and its positive counterpart.
        for case in range(10):
          for sign in (-1,1):
            values={n:1 for n in p['parameters']+p['auxiliaries']};values[f'hist__Shat{case}']=2
            preliminary=execute(cone,values);P=preliminary['hist__P__63']
            values[PORTS[case]]=P-9-(2 if sign==1 else 0)
            e=execute(cone,values)
            assert e[GLOBAL]==sign and sum(values[n] for n in PORTS)<=P
            assert all(0<values[n]<P for n in PORTS)
            assert e['hist__and__F3']>=8 and e['and__F3']>=8
            counts['literal_weak_global_endpoint_contexts']+=1
    # Independent typed components, using actual disjoint slope classes.
    hp=build()['history_packet']
    for D in (2,4,8,32):
      for duration in range(1,5):
        B=hp['K']*D;P=B**duration;J=(P-1)//(B-1)
        for trial in range(16):
            chosen=[rng.randrange(57) for _ in range(duration)]
            digits=[[rng.randrange(D) for _ in range(duration)] for _ in range(2)]
            histories=[sum(v*B**i for i,v in enumerate(row)) for row in digits]
            selected=[]
            for side,key in enumerate(('groups_U','groups_V')):
                masks=[set(g['tiles']) for g in hp[key]]
                assert all(len([1 for group in masks if tile in group])<=1 for tile in range(57))
                selected.append([sum(digits[side][i]*B**i for i,tile in enumerate(chosen) if tile in group) for group in masks])
                assert sum(selected[-1])<=histories[side]
            Sigma=sum(histories)+sum(sum(v+1 for v in row) for row in selected)
            assert Sigma<=2*sum(histories)+8<=4*(D-1)*J+8
            beta=P-Sigma
            assert beta>=(131068*D+3)*J-7>1 and P-Sigma-(beta-1)==1
            counts['typed_inverse_slack_components']+=1
    return dict(counts)


def guards():
    count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError,TypeError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for inline in (False,True):
        old=parent.build(inline_initial=inline)
        for key,value in [('source',old['source'][:-1]),('comparisons',[]),('unit_factors',[]),
                          ('parameters',[]),('auxiliaries',[]),('machine',{}),('program_code','bad'),
                          ('inline_initial',int(inline)),('regroup',False)]:
            reject(lambda key=key,value=value:rewrite(dict(old,**{key:value})))
        for global_unit in (False,True):
            p=build(inline_initial=inline,global_unit=global_unit)
            for key,value in [('source',p['source'][:-1]),('unit_register',CHECKSUM),('comparisons',[]),
                              ('history_global_unit',int(global_unit)),('positive_zero_bijection','unrestricted identity')]:
                for api in (polynomial_source,degree_dictionary,degree_audit,ledger):
                    reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
    reject(lambda:build(inline_initial=1));reject(lambda:build(global_unit=0))
    return count


def verify():
    forms=[]
    for inline in (False,True):
      for global_unit in (False,True):
        p=build(inline_initial=inline,global_unit=global_unit);rows,out=polynomial_source(p)
        record=ledger(p)
        lookup={n:(a,b) for n,_,a,b in rows};need=set();todo=[out]
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in lookup and n not in need:need.add(n);todo.extend(lookup[n])
        assert need==lookup.keys()
        want=(771 if global_unit else 772) if inline else (774 if global_unit else 775)
        degree=(209782 if global_unit else 209715) if inline else (8672 if global_unit else 8670)
        assert record['polynomial']['operations']==want and record['degree']['exact_degree']==degree
        assert p['witnesses']==(125 if inline else 126)
        record.update(inline_initial=inline,global_unit=global_unit,source=rows,output=out,
            comparisons=p['comparisons'],parameters=p['parameters'],auxiliaries=p['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        forms.append(record)
    return dict(status='PASS_GPCP_CHECKSUM_GLOBAL_UNITS771',forms=forms,source_audit=source_audit(),
        signs=sign_audit(),positive_cones=positive_cone_audit(),rejected_callers=guards(),
        scope='Checksum-only forms have the same full supplied positive zeros; global-unit forms have the full positive bijection beta_parent=beta_new+1. All fixed U15,2 program/input data are retained. Fixtures are algebra/components, not complete Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print({k:v for k,v in result.items() if k not in ('forms','status')})
