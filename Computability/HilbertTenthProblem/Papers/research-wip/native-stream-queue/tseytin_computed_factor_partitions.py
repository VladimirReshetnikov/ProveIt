"""Exact finite factor-group/anchor planning for the computed-field Tseytin399.

Two word-strong bases, fixed exponent52, actual24-tile C2 and paid input
loader. Within one base all plans have the same full positive zeros on
valid program slices. Across strong bases only accepted-input equivalence
with fresh auxiliary extensions is asserted.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path
import random

import tseytin_adjacent_coefficients399 as parent
import pell_fixed_affine_exponent52 as power
import neary_woods_universal_joint_and_coupled_partitions as optimizer

computed=parent.parent
word=computed.word
scale=word.scale
execute=parent.execute
STRONG='and__f_square_minus_one'
QSTRONG='and__normalized_strong_Q'
EXPECTED=[(399,4712),(400,4132),(402,2900),(404,2210),(406,1664)]


def closure(rows,roots):
    lookup={n:(a,b) for n,_,a,b in rows};seen=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in lookup and n not in seen:
            seen.add(n);pending.extend(lookup[n])
    return [r for r in rows if r[0] in seen]


def _strong_guard(rows):
    required={
        'and__L16':('*','and__f','and__f'),
        'and__ic2':('*','and__i','and__c2'),
        'and__ic22':('*','and__ic2','and__ic2'),
        QSTRONG:('*','and__A','and__ic22'),
        STRONG:('-','and__L16',QSTRONG),
        'and__R16':('*','and__A',QSTRONG),
        'and__L17':('*','and__R16','and__aux_square_gap'),
        'and__P17':('+','and__L17','and__aux_y2'),
        'and__H2':('*','and__aux_u_rhs','and__aux_u_rhs'),
        'and__aux_square_gap':('-','and__H2','and__aux_y2'),
        'and__aux_u_rhs':('-','and__of','and__R10a')}
    actual={n:(o,a,b) for n,o,a,b in rows}
    assert all(actual.get(n)==v for n,v in required.items())
    for name,want in [('and__i',{'and__ic2'}),('and__ic2',{'and__ic22'}),
                      ('and__ic22',{QSTRONG}),(QSTRONG,{STRONG,'and__R16'}),
                      ('and__R16',{'and__L17'})]:
        assert {n for n,_,a,b in rows if name in (a,b)}==want


@lru_cache(None)
def _base(normalized):
    assert type(normalized) is bool
    old=parent.build();parent.checked_packet(old)
    assert old['checksum_fixed_one'] and old['computed_truth_fields'] and old['native_inner_bound']
    assert not {'and__F0','and__F1','and__F2'}&set(old['auxiliaries'])
    assert old['word_factors']==['and__R15','and__P17','and__first_unit',STRONG,'and__index_unit','and__linear_unit']
    rows=list(old['source']);_strong_guard(rows)
    factors=list(old['word_factors'])+list(old['power_factors'])
    pairs=list(old['ordinary_comparisons'])
    assert len(pairs)==4 and len(factors)==12 and len(old['auxiliaries'])==62
    if not normalized:
        change={STRONG:('-','and__L16',1),'and__R16':('*','and__A',STRONG)}
        rows=[(n,*change.get(n,(o,a,b))) for n,o,a,b in rows]
        factors.remove(STRONG);pairs.append(('and__ic22','and__R16'))
    rows=closure(rows,factors+[v for pair in pairs for v in pair])
    # Canonical auxiliary reconstruction may change exactly these five.
    # Main data, truth fields/index and all outer comparisons are independent.
    rebuilt={'and__'+n for n in ('f','i','j','o','y_aux')}
    deps={n:({n} if n in rebuilt else set()) for n in old['parameters']+old['auxiliaries']}
    dep=lambda v:deps[v] if isinstance(v,str) else set()
    for n,_,a,b in rows:deps[n]=dep(a)|dep(b)
    stable=['and__q','and__bs_packed','and__factored_index_inner','and__wn2','and__sn2',
            'and__R12','and__R10a','and__root_base','and__R15','and__first_unit','and__index_unit']
    stable+=old['power_factors']
    stable += [v for pair in old['ordinary_comparisons'] for v in pair]
    assert all(not dep(v)&rebuilt for v in stable)
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    assert len(rows)==(374 if normalized else 373)
    return dict(source=rows,factor_source=rows,parameters=list(old['parameters']),
        auxiliaries=list(old['auxiliaries']),unit_factors=factors,
        ordinary_comparisons=pairs,word_strong_normalized=normalized,
        interfaces=deepcopy(old['interfaces']),program_recipe=old['program_recipe'],
        positive_integer_domain=True,tseytin_computed_factor_base=True,
        checksum_fixed_one=True,native_inner_bound=True,
        projection='On valid program slices, identical full supplied positive zero sets within each strong base; accepted-input equivalence across strong bases with fresh five-coordinate extensions.')


def base(normalized=True):return deepcopy(_base(normalized))


def grouped(original,partition,anchor):
    assert original==base(original['word_strong_normalized']),'complete canonical factor base required'
    nf=len(original['unit_factors']);partition=[list(g) for g in partition]
    assert partition and all(partition)
    assert all(type(i) is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g)==list(range(nf))
    assert anchor is None or (type(anchor) is int and 0<=anchor<len(partition))
    rows=list(original['source']);products=[]
    for j,g in enumerate(partition):
        value=original['unit_factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name=f'tseytin_partition_group{j}_{k}'
            assert name not in {n for n,_,_,_ in rows}|set(original['parameters']+original['auxiliaries'])
            rows.append((name,'*',value,original['unit_factors'][i]));value=name
        products.append(value)
    last=len(products)-1 if anchor is None else anchor
    comparisons=list(original['ordinary_comparisons'])+[(p,1) for j,p in enumerate(products) if j!=last]+[(products[last],1)]
    packet=scale.metadata(dict(original,source=rows,comparisons=comparisons,
        unit_register=products[last],group_products=products,
        factor_partition=partition,partition_anchor=anchor,tseytin_factor_partition=True,
        identical_complete_polynomial_to399=original['word_strong_normalized'] and partition==[list(range(nf))] and anchor==0,
        identical_fixed_base_positive_zero_set=True,
        positive_zero_equality_scope='valid program slices only'))
    scale.checked_source(rows,packet['parameters'],packet['auxiliaries'])
    return packet


def checked_packet(packet):
    assert packet==grouped(base(packet['word_strong_normalized']),packet['factor_partition'],packet['partition_anchor']), 'complete canonical grouped packet required'


def polynomial_source(packet):
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=packet['partition_anchor'] is None)


def degree_dictionary(packet):
    """Literal propagation plus the two guarded all-integer norm identities."""
    source=packet['source'];rows={n:(o,a,b) for n,o,a,b in source}
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    d=lambda v:degrees[v] if isinstance(v,str) else 0
    a,c='and__R12','and__R10a';X,G='and__wn2','and__gam'
    expected={'and__R15':('-','and__L15','and__Ac2'),'and__L15':('*','and__R14','and__R14'),
        'and__R14':('+','and__D1',G),'and__D1':('+',X,'and__cam2'),
        'and__cam2':('*',c,a),'and__A':('+','and__a_square','and__a4m5'),
        'and__a_square':('*',a,a),'and__a4m5':('+','and__a4',3),'and__a4':('*',4,a),
        G:('*','and__ga','and__a4m5'),'and__Ac2':('*','and__A','and__c2'),
        'and__c2':('*',c,c)}
    assert all(rows.get(n)==v for n,v in expected.items())
    exponent={(('exp__'+n) if isinstance(n,str) and n!='x' else n):
                  (o,('exp__'+a) if isinstance(a,str) and a!='x' else a,
                   ('exp__'+b) if isinstance(b,str) and b!='x' else b)
              for n,o,a,b in power.build()['source']}
    assert all(rows[n]==v for n,v in exponent.items() if n in rows)
    for n,o,u,v in source:
        degrees[n]=d(u)+d(v) if o=='*' else max(d(u),d(v))
        if n=='and__R15':
            degrees[n]=max(2*d(X),d(X)+d(a)+d(c),d(X)+d(G),d(a)+d(c)+d(G),2*d(G),d('and__a4m5')+2*d(c))
        elif n=='exp__N1':
            degrees[n]=max(2*d('exp__L'),d('exp__L')+d('exp__a')+d('exp__c'),d('exp__H')+2*d('exp__c'))
    return degrees


def degree_bound(packet):
    checked_packet(packet);degrees=degree_dictionary(packet)
    d=lambda v:degrees[v] if isinstance(v,str) else 0
    weights=[d(f) for f in packet['unit_factors']]
    residual=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons'])
    groups=[sum(weights[i] for i in g) for g in packet['factor_partition']]
    assert groups==[d(p) for p in packet['group_products']]
    anchor=packet['partition_anchor']
    bound=2*max([residual]+groups) if anchor is None else groups[anchor]+2*max([residual]+[v for j,v in enumerate(groups) if j!=anchor])
    return dict(degree_upper_bound=bound,factor_degree_bounds=weights,
        maximum_original_residual_degree_bound=residual,group_degree_bounds=groups,exact_degree_claimed=False)


def ledger(packet):
    source,out=polynomial_source(packet);c=Counter(o for _,o,_,_ in source)
    nf=len(packet['unit_factors']);g=len(packet['factor_partition']);m=len(packet['ordinary_comparisons']);core=len(packet['factor_source'])
    assert len(source)==core+nf+3*m-1+2*g
    assert len(closure(source,[out]))==len(source)
    return dict(normalized=packet['word_strong_normalized'],partition=packet['factor_partition'],anchor=packet['partition_anchor'],
        core_operations=core,ordinary_comparisons=m,factor_names=packet['unit_factors'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],**degree_bound(packet)))


@lru_cache(None)
def search(normalized):
    original=base(normalized);nf=len(original['unit_factors'])
    initial=grouped(original,[list(range(nf))],0);degree=degree_bound(initial)
    weights=degree['factor_degree_bounds'];r=degree['maximum_original_residual_degree_bound']
    plans,statistics=optimizer.optimal_partitions(weights,r)
    records=[]
    for plan in plans:
        packet=grouped(original,plan['partition'],plan['anchor']);record=ledger(packet)
        assert record['polynomial']['degree_upper_bound']==plan['degree_upper_bound']
        records.append(record)
    # With arbitrarily many groups, the other factors can be singletons.
    # Enumerating the distinguished subset gives an exact global floor for
    # this finite propagated objective, including the SOS competitor.
    floor=2*max([r]+weights);argmin=None
    for mask in range(1,1<<nf):
        anchored=sum(w for i,w in enumerate(weights) if mask>>i&1)
        other=max([r]+[w for i,w in enumerate(weights) if not mask>>i&1])
        if anchored+2*other<floor:floor=anchored+2*other;argmin=mask
    assert min(t['polynomial']['degree_upper_bound'] for t in records)==floor
    return dict(normalized=normalized,statistics=statistics,best_by_group_count=records,
        floor_certificate=dict(lower_bound=floor,anchor_mask=argmin,anchor_masks_checked=(1<<nf)-1,
            attained_operations=min(t['polynomial']['operations'] for t in records if t['polynomial']['degree_upper_bound']==floor)))


def frontier(normalized=None):
    assert normalized is None or type(normalized) is bool
    candidates=[r for n in ((False,True) if normalized is None else (normalized,)) for r in search(n)['best_by_group_count']]
    candidates.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']))
    result=[];bound=float('inf')
    for row in candidates:
        if row['polynomial']['degree_upper_bound']<bound:result.append(row);bound=row['polynomial']['degree_upper_bound']
    return result


def build(operations=406,*,normalized=None):
    choice=next(r for r in frontier(normalized) if r['polynomial']['operations']==operations)
    return grouped(base(choice['normalized']),choice['partition'],choice['anchor'])


def grouping_audit(packet,cases=16,seed=399406):
    source,out=polynomial_source(packet);rng=random.Random(seed);totals=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        v={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        # Zero decoded selectors are meaningful adversarial source assignments.
        if case%8==0:v.update({f'Shat{i}':1 for i in range(24)})
        before=execute(packet['factor_source'],v);e=execute(source,v)
        assert all(e[n]==before[n] for n,_,_,_ in packet['factor_source'])
        at=lambda a:before[a] if isinstance(a,str) else a
        groups=[prod(before[packet['unit_factors'][i]] for i in g) for g in packet['factor_partition']]
        assert groups==[e[n] for n in packet['group_products']]
        residual=sum((at(a)-at(b))**2 for a,b in packet['ordinary_comparisons'])
        anchor=packet['partition_anchor']
        residual+=sum((g-1)**2 for j,g in enumerate(groups) if j!=anchor)
        expected=residual if anchor is None else groups[anchor]*(1+residual)-1
        assert e[out]==expected
        totals['complete_register_and_manual_finalizer_identities']+=1;totals['signed_identities']+=signed
    return dict(totals)


def base_map_audit(cases=64):
    """Formal positive forward i_old=Delta*i; no off-zero polynomial identity."""
    a,b=base(True),base(False);rng=random.Random(399407);totals=Counter()
    changed={'and__ic2','and__ic22',STRONG,'and__R16','and__L17','and__P17'}
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        v={n:draw() for n in a['parameters']+a['auxiliaries']};e=execute(a['source'],v)
        lifted=dict(v,**{'and__i':e['and__A']*v['and__i']});f=execute(b['source'],lifted)
        Delta,N=e['and__A'],e[STRONG]
        assert f['and__ic22']-f['and__R16']==Delta*(1-N)
        assert f['and__P17']==e['and__P17']+Delta*(N-1)*e['and__aux_square_gap']
        assert all(f[n]==e[n] for n,_,_,_ in b['source'] if n not in changed)
        if not signed:assert min(lifted.values())>0;totals['positive_forward_maps']+=1
        totals['full_retained_source_and_corrected_factor_maps']+=1;totals['signed_maps']+=signed
    # One normalized all-factor anchor has exactly the parent's polynomial,
    # although its product tree/labels are deliberately rebuilt.
    p=grouped(a,[list(range(12))],0);s,out=polynomial_source(p);old=parent.build();t,target=parent.polynomial_source(old)
    for case in range(cases):
        v={n:rng.randrange(-2,4) for n in p['parameters']+p['auxiliaries']}
        assert execute(s,v)[out]==execute(t,v)[target]
        totals['canonical399_complete_polynomial_identities']+=1
    return dict(totals)


def signs_audit():
    cases=accepted=0
    for normalized in (False,True):
        original=base(normalized);word_count=len(original['unit_factors'])-6
        for rec in search(normalized)['best_by_group_count']:
            partition=rec['partition']
            assert all(prod([1 for _ in g])==1 for g in partition)
            for signs in product((-1,1),repeat=len(original['unit_factors'])):
                groups=[prod(signs[i] for i in g) for g in partition];cases+=1
                if all(g==1 for g in groups):
                    assert prod(signs)==1
                    # The loader's separate theorem supplies P=+1; only then
                    # infer W=+1. No semantic claim at arbitrary I is used.
                    if prod(signs[word_count:])==1:
                        assert prod(signs[:word_count])==1;accepted+=1
    return dict(finite_factor_sign_assignments=cases,group_and_filtered_power_acceptances=accepted,
        scope='Finite unit-sign algebra only; not native positive Pell zeros.')


def pretyping_audit():
    totals=Counter();normalized=base(True);ordinary=base(False)
    words=['H_U','H_V']+[f'Z{side}hat{i}' for side in ('U','V') for i in range(4)]
    for D in (1,3,4,9,32):
      for J in (1,2,5,17):
       for tile in (0,5,9,14,17,23):
        for heavy in (-1,0,2,6,9):
            packet=ordinary if (tile+heavy)%2 else normalized
            values={n:1 for n in packet['parameters']+packet['auxiliaries']}
            values['height_slack']=D;values[f'Shat{tile}']=J+1
            B=65536*D;P=(B-1)*J+1
            if heavy>=0:values[words[heavy]]=P-10
            values['global_bound']=P-sum(values[n] for n in words)
            assert min(values.values())>0
            e=execute(packet['source'],values)
            assert e['global_lhs__40']==e['P__30']==P
            H,M,Z=(e[n] for n in ('joined_H__287','joined_M__293','joined_Z__294'))
            T=P**34;q=e['and__q'];assert q==16*B*T
            assert 0<=H-2*T<T and 0<=M-T<T and 0<=Z<T
            assert H-Z>=T+1 and M-Z>=1 and B*T-H-M+Z>=(B-5)*T+2
            A,C,Zp=16*H+12,16*M+10,16*Z+8
            fields=[q-A-C+Zp-1,A-Zp,C-Zp,Zp]
            assert min(fields)>0 and sum(fields)==q-1
            assert [f%16 for f in fields]==[1,4,2,8]
            r=sum(f*q**i for i,f in enumerate(fields));S=A+1+(q+1)*(C+(q-1)*Zp)
            assert r==e['and__bs_packed']==(q-1)*S and S==e['and__factored_index_inner']
            assert sum(q**i for i in range(4))<=r<q**4 and r>q and r%16==1
            X,Y=e['and__wn2'],e['and__sn2'];assert X==q*(S+values['and__bound_beta'])>r
            assert Y>=3*q and X*Y>2*r+3 and Y*(r-1)>2*(2*r+3)
            totals['actual_source_pretyping_contexts']+=1
            totals['height_one_contexts']+=D==1
            totals['nondyadic_scale_contexts']+=q&(q-1)!=0
    return dict(totals,scope='Actual scalar source contexts satisfying only the positive global bound; no native/Pell zero or selector typing assumed.')


def local_sign_audit():
    # At a unit zero, ordinary strong equality makes the auxiliary norm
    # coefficient a square. Check the unconditional modulo-four exclusions.
    cases=0
    for a in range(16):
      Delta=(a+2)**2-1
      for root in range(8):
       for ordinate in range(8):
        assert (root*root-Delta*ordinate*ordinate)%4!=3
        assert (root*root+4*Delta*ordinate)%4!=3
        for T in range(8):
            assert (T*T*(root*root-ordinate*ordinate)+ordinate*ordinate)%4!=3
            cases+=1
    # The local rank/ratio proof supplies lambda=+1. The independent loader
    # supplies the power product+1; no leftover checksum can absorb Nk.
    signs=0
    for epsilon in (-1,1):
      for lam in (-1,1):
       for exponent_product in (-1,1):
        if epsilon*lam*exponent_product==1 and lam==1 and exponent_product==1:
            assert epsilon==1;signs+=1
    return dict(norm_modulo_four_contexts=cases,remaining_unit_sign_patterns=signs,
        scope='Finite sign algebra supplement to the explicit local rank proof.')


def guards():
    p=base();bad=[dict(p,source=p['source'][:-1]),dict(p,interfaces={'initial':'word'}),
        dict(p,program_recipe='arbitrary positive A'),dict(p,auxiliaries=p['auxiliaries'][:-1])]
    for q in bad:
        try:grouped(q,[list(range(12))],0)
        except AssertionError:pass
        else:raise AssertionError('noncanonical base accepted')
    malformed=[([[0]],0),([[]],None),([list(range(12))],True),([list(range(12))],1),
        ([list(range(11))+[True]],None),([list(range(11))+[10]],None)]
    for partition,anchor in malformed:
        try:grouped(p,partition,anchor)
        except AssertionError:pass
        else:raise AssertionError('invalid plan accepted')
    q=build();altered=[dict(q,source=q['source'][:-1]),dict(q,comparisons=q['comparisons'][:-1]),
        dict(q,unit_register=q['unit_factors'][0]),dict(q,identical_fixed_base_positive_zero_set=False)]
    for packet in altered:
        for call in (polynomial_source,degree_bound):
            try:call(packet)
            except AssertionError:pass
            else:raise AssertionError('altered grouped packet accepted')
    return len(bad)+len(malformed)+2*len(altered)


def verify():
    studies=[search(n) for n in (False,True)];records=[];totals=Counter()
    for study in studies:
        for rec in study['best_by_group_count']:
            packet=grouped(base(study['normalized']),rec['partition'],rec['anchor'])
            result=ledger(packet);result['audit']=grouping_audit(packet,seed=399500+len(records));totals.update(result['audit'])
            records.append(result)
    frontiers={str(n):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in frontier(n)] for n in (None,False,True)}
    assert frontiers['None']==EXPECTED
    assert frontiers['True']==[(399,4712),(401,4705),(403,3608)]
    assert frontiers['False']==[(400,4132),(402,2900),(404,2210),(406,1664)]
    examples=[]
    seen=set()
    for n in (None,False,True):
      for rec in frontier(n):
        key=(rec['normalized'],tuple(map(tuple,rec['partition'])),rec['anchor'])
        if key in seen:continue
        seen.add(key);packet=grouped(base(key[0]),rec['partition'],rec['anchor']);source,out=polynomial_source(packet)
        result=ledger(packet);result.update(source=source,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            comparisons=packet['comparisons'],source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest());examples.append(result)
    # Further nonoptimal plans exercise arbitrary group order and every anchor.
    for normalized in (False,True):
        b=base(normalized);n=len(b['unit_factors']);partition=[list(range(i,n,4)) for i in range(4)]
        for anchor in (None,0,1,2,3):totals.update(grouping_audit(grouped(b,partition,anchor),seed=406000+int(normalized)*10+(anchor or 0)))
    return dict(status='PASS_TSEYTIN_COMPUTED_FACTOR_PARTITIONS',studies=studies,ledgers=records,frontiers=frontiers,
        selected_sources=examples,output_audits=dict(totals),base_maps=base_map_audit(),unit_signs=signs_audit(),
        independent_small_search=optimizer.small_exhaustive_checks(),sign_filter=parent.base.sign_filter(),
        pretyping=pretyping_audit(),local_signs=local_sign_audit(),
        rejected_mutations=guards(),scope='Two fixed strong bases, disjoint factor partitions, SOS or one-anchor finalizers. Exact finite propagated cost/degree objective only; same supplied positive zeros on valid slices within each base, accepted-input equivalence across bases through fresh auxiliaries; not exact expanded polynomial degrees.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['output_audits'])
