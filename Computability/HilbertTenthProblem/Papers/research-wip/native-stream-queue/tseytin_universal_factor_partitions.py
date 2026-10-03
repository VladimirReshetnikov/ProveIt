"""Exact finite factor-group/anchor planning for the complete Tseytin425.

Two word-strong bases, fixed exponent52, actual24-tile C2 and paid input
loader. Each plan has the same accepted valid-program input relation;
no equality of arbitrary supplied positive zero tuples is asserted.
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

import tseytin_universal425 as parent
import neary_woods_universal_joint_and_coupled_partitions as optimizer

word=parent.word
scale=word.scale
execute=parent.execute
STRONG='and__f_square_minus_one'
QSTRONG='and__normalized_strong_Q'
EXPECTED=[(425,5868),(426,5140),(428,3578),(430,2720),(432,2012)]


def closure(rows,roots):
    lookup={n:(a,b) for n,_,a,b in rows};seen=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in lookup and n not in seen:
            seen.add(n);pending.extend(lookup[n])
    return [r for r in rows if r[0] in seen]


def reference_word(normalized):
    """A complete inherited word/native embedding, before exact outer sharing."""
    return word.coupled.rewrite(word.norms.rewrite(word.build('fields'),normalized=normalized))


@lru_cache(None)
def _base(normalized):
    assert type(normalized) is bool
    old=parent.build();rows=list(old['source'])
    factors=list(old['word_factors'])+list(old['power_factors'])
    pairs=list(old['ordinary_comparisons'])
    definitions={n:(o,a,b) for n,o,a,b in rows}
    assert definitions[STRONG]==('-','and__L16',QSTRONG)
    assert definitions[QSTRONG]==('*','and__A','and__ic22')
    assert definitions['and__R16']==('*','and__A',QSTRONG)
    assert {n for n,_,a,b in rows if QSTRONG in (a,b)}=={STRONG,'and__R16'}
    if not normalized:
        change={STRONG:('-','and__L16',1),'and__R16':('*','and__A',STRONG)}
        rows=[(n,*change.get(n,(o,a,b))) for n,o,a,b in rows]
        factors.remove(STRONG);pairs.append(('and__ic22','and__R16'))
    rows=closure(rows,factors+[v for pair in pairs for v in pair])
    # This is the actual complete original/normalized native core, not an
    # unproved formal reversal of the strong substitution.
    reference=reference_word(normalized)
    native_roots=[f for f in factors if f.startswith('and__')]
    native_roots += [v for pair in pairs for v in pair if isinstance(v,str) and v.startswith('and__')]
    ref={n:(o,a,b) for n,o,a,b in closure(reference['source'],native_roots) if n.startswith('and__')}
    actual={n:(o,a,b) for n,o,a,b in rows if n.startswith('and__')}
    assert actual==ref
    assert factors[:len(reference['unit_factors'])]==reference['unit_factors']
    assert all(pair in pairs for pair in reference['comparisons'][:-1] if pair[0].startswith('and__'))
    scale.checked_source(rows,old['parameters'],old['auxiliaries'])
    assert len(rows)==(393 if normalized else 392)
    return dict(source=rows,factor_source=rows,parameters=list(old['parameters']),
        auxiliaries=list(old['auxiliaries']),unit_factors=factors,
        ordinary_comparisons=pairs,word_strong_normalized=normalized,
        interfaces=deepcopy(old['interfaces']),program_recipe=old['program_recipe'],
        positive_integer_domain=True,tseytin_factor_base=True,
        projection='Same accepted ordinary positive inputs on the inherited valid one-program slices, through fresh positive extensions. No tuple-zero equality across partitions or bases claimed.')


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
        identical_complete_polynomial_to425=original['word_strong_normalized'] and partition==[list(range(nf))] and anchor==0,
        identical_positive_zero_set_claimed=False))
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
    native=reference_word(packet['word_strong_normalized'])
    alias=lambda k:native['computed_substitutions'].get('and__'+k,'and__'+k)
    a,c=alias('a'),alias('c');X,G='and__wn2','and__gam'
    expected={'and__R15':('-','and__L15','and__Ac2'),'and__L15':('*','and__R14','and__R14'),
        'and__R14':('+','and__D1',G),'and__D1':('+',X,'and__cam2'),
        'and__cam2':('*',c,a),'and__A':('+','and__a_square','and__a4m5'),
        'and__a_square':('*',a,a),'and__a4m5':('+','and__a4',3),'and__a4':('*',4,a),
        G:('*','and__ga','and__a4m5'),'and__Ac2':('*','and__A','and__c2'),
        'and__c2':('*',c,c)}
    assert all(rows.get(n)==v for n,v in expected.items())
    exponent={parent.exponent_name(n):(o,parent.exponent_name(a),parent.exponent_name(b))
              for n,o,a,b in parent.power.build()['source']}
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


def build(operations=432,*,normalized=None):
    choice=next(r for r in frontier(normalized) if r['polynomial']['operations']==operations)
    return grouped(base(choice['normalized']),choice['partition'],choice['anchor'])


def grouping_audit(packet,cases=16,seed=425432):
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
    a,b=base(True),base(False);rng=random.Random(425433);totals=Counter()
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
    p=grouped(a,[list(range(13))],0);s,out=polynomial_source(p);old=parent.build();t,target=parent.polynomial_source(old)
    for case in range(cases):
        v={n:rng.randrange(-2,4) for n in p['parameters']+p['auxiliaries']}
        assert execute(s,v)[out]==execute(t,v)[target]
        totals['canonical425_complete_polynomial_identities']+=1
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


def guards():
    p=base();bad=[dict(p,source=p['source'][:-1]),dict(p,interfaces={'initial':'word'}),
        dict(p,program_recipe='arbitrary positive A'),dict(p,auxiliaries=p['auxiliaries'][:-1])]
    for q in bad:
        try:grouped(q,[list(range(13))],0)
        except AssertionError:pass
        else:raise AssertionError('noncanonical base accepted')
    malformed=[([[0]],0),([[]],None),([list(range(13))],True),([list(range(13))],1),
        ([list(range(12))+[True]],None),([list(range(12))+[11]],None)]
    for partition,anchor in malformed:
        try:grouped(p,partition,anchor)
        except AssertionError:pass
        else:raise AssertionError('invalid plan accepted')
    q=build();altered=[dict(q,source=q['source'][:-1]),dict(q,comparisons=q['comparisons'][:-1]),
        dict(q,unit_register=q['unit_factors'][0]),dict(q,identical_positive_zero_set_claimed=True)]
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
            result=ledger(packet);result['audit']=grouping_audit(packet,seed=425500+len(records));totals.update(result['audit'])
            records.append(result)
    frontiers={str(n):[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in frontier(n)] for n in (None,False,True)}
    assert frontiers['None']==EXPECTED
    assert frontiers['True']==[(425,5868),(427,5802),(429,4316)]
    assert frontiers['False']==[(426,5140),(428,3578),(430,2720),(432,2012)]
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
        for anchor in (None,0,1,2,3):totals.update(grouping_audit(grouped(b,partition,anchor),seed=426000+int(normalized)*10+(anchor or 0)))
    return dict(status='PASS_TSEYTIN_UNIVERSAL_FACTOR_PARTITIONS',studies=studies,ledgers=records,frontiers=frontiers,
        selected_sources=examples,output_audits=dict(totals),base_maps=base_map_audit(),unit_signs=signs_audit(),
        independent_small_search=optimizer.small_exhaustive_checks(),sign_filter=parent.sign_filter(),
        rejected_mutations=guards(),scope='Two fixed strong bases, disjoint factor partitions, SOS or one-anchor finalizers. Exact finite propagated cost/degree objective only; same universal accepted-input relation with fresh positive extensions, not all supplied zero tuples or exact expanded polynomial degrees.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['output_audits'])
