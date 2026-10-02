"""Exact finite grouping degrees for the asymmetric complete87/88 sources.

Three canonical bases: normalized units, ordinary units, and ordinary
strong comparison. Grouping preserves each base's full positive zeros.
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

import sympy as sp
import complete75_asymmetric_scale_tradeoffs as parent
import neary_woods_universal_joint_and_coupled_partitions as optimizer

KINDS=('normalized_units','ordinary_units','ordinary_comparison')
EXPECTED=[(87,169),(88,125),(91,104),(93,72),(95,64)]


def ancestors(rows,roots):
    nodes={n:(a,b) for n,_,a,b in rows};seen=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in nodes and n not in seen:
            seen.add(n);pending.extend(nodes[n])
    return [row for row in rows if row[0] in seen]


def base(kind):
    assert kind in KINDS
    normalized=kind=='normalized_units'
    original=parent.source(normalized)
    factors=list(parent.FACTOR_NAMES)
    weights=list(parent.FACTOR_DEGREES[normalized])
    comparisons=[]
    if kind=='ordinary_comparison':
        nodes={n:(o,a,b) for n,o,a,b in original}
        assert nodes['strong_difference']==('-','ic22','R16')
        assert nodes['norm_strong']==('+','strong_difference',1)
        i=factors.index('norm_strong');factors.pop(i);weights.pop(i)
        comparisons=[('ic22','R16')]
    rows=ancestors(original,factors+[v for pair in comparisons for v in pair])
    assert len(rows)==dict(normalized_units=79,ordinary_units=80,ordinary_comparison=78)[kind]
    return dict(kind=kind,source=rows,factors=factors,weights=weights,
                ordinary_comparisons=comparisons,residual_degree=22 if comparisons else 0,
                auxiliaries=list(parent.RETAINED),input='x',
                fixed_compiler_contract='Unchanged actual complete75 compiler numerals and ordinary positive input.',
                positive_zero_scope='Same supplied positive zero set as the corresponding asymmetric87/88 parent; cross-strong-treatment equivalence is existential.')


def grouped(original,partition,anchor):
    assert original==base(original['kind']),'complete canonical asymmetric factor base required'
    partition=[list(g) for g in partition]
    n=len(original['factors'])
    assert partition and all(partition)
    assert all(type(i) is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g)==list(range(n))
    assert anchor is None or (type(anchor) is int and 0<=anchor<len(partition))
    rows=list(original['source']);products=[];names={r[0] for r in rows}|set(parent.RETAINED+['x'])
    for j,g in enumerate(partition):
        value=original['factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name=f'asym_group_{j}_{k}';assert name not in names;names.add(name)
            rows.append((name,'*',value,original['factors'][i]));value=name
        products.append(value)
    return dict(original,source=rows,partition=partition,anchor=anchor,group_products=products)


def checked(packet):
    assert packet==grouped(base(packet['kind']),packet['partition'],packet['anchor']), 'complete canonical grouped source required'


def polynomial_source(packet):
    checked(packet)
    rows=list(packet['source']);anchor=packet['anchor'];products=packet['group_products']
    pairs=list(packet['ordinary_comparisons'])+[(v,1) for j,v in enumerate(products) if j!=anchor]
    last=None
    for i,(a,b) in enumerate(pairs):
        residual=f'asym_residual_{i}';square=f'asym_square_{i}'
        rows.extend([(residual,'-',a,b),(square,'*',residual,residual)])
        if last is None:last=square
        else:
            add=f'asym_sum_{i}';rows.append((add,'+',last,square));last=add
    if anchor is None:
        assert last is not None
        return rows,last
    unit=products[anchor]
    if last is None:
        rows.append(('asym_output','-',unit,1))
    else:
        rows.extend([('asym_positive','+',last,1),('asym_product','*',unit,'asym_positive'),
                     ('asym_output','-','asym_product',1)])
    return rows,'asym_output'


def exact_degree(packet):
    checked(packet)
    gs=[sum(packet['weights'][i] for i in g) for g in packet['partition']]
    a=packet['anchor'];r=packet['residual_degree']
    value=2*max([r]+gs) if a is None else gs[a]+2*max([r]+[d for j,d in enumerate(gs) if j!=a])
    return dict(exact_degree=value,group_degrees=gs,factor_degrees=packet['weights'],
                original_residual_degree=r)


def record(packet):
    rows,out=polynomial_source(packet);c=Counter(o for _,o,_,_ in rows)
    n=len(packet['factors']);g=len(packet['partition']);m=len(packet['ordinary_comparisons'])
    core=len(base(packet['kind'])['source'])
    special=m==0 and g==1 and packet['anchor']==0
    assert len(rows)==core+n+3*m+2*g-1-int(special)
    assert len(ancestors(rows,[out]))==len(rows)
    return dict(kind=packet['kind'],partition=packet['partition'],anchor=packet['anchor'],
        core_operations=core,certificate_operations=len(packet['source']),equations=m+g,
        witnesses=19,operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],
        empty_residual_product_finalizer=special,**exact_degree(packet))


@lru_cache(None)
def search(kind):
    original=base(kind)
    plans,statistics=optimizer.optimal_partitions(original['weights'],original['residual_degree'])
    records=[]
    for plan in plans:
        p=grouped(original,plan['partition'],plan['anchor']);r=record(p)
        assert r['exact_degree']==plan['degree_upper_bound']
        records.append(r)
    return dict(kind=kind,statistics=statistics,best_by_group_count=records)


def frontier():
    candidates=[r for k in KINDS for r in search(k)['best_by_group_count']]
    candidates.sort(key=lambda r:(r['operations'],r['exact_degree'],r['kind']))
    answer=[];best=float('inf')
    for r in candidates:
        if r['exact_degree']<best:answer.append(r);best=r['exact_degree']
    assert [(r['operations'],r['exact_degree']) for r in answer]==EXPECTED
    return deepcopy(answer)


def build(operations=95):
    r=next(r for r in frontier() if r['operations']==operations)
    return grouped(base(r['kind']),r['partition'],r['anchor'])


def bell_partitions(n):
    """Independent restricted-growth enumeration; no subset-DP helper used."""
    groups=[]
    def visit(i):
        if i==n:
            yield [g[:] for g in groups];return
        for g in groups:
            g.append(i);yield from visit(i+1);g.pop()
        groups.append([i]);yield from visit(i+1);groups.pop()
    yield from visit(0)


def independent_objectives():
    records=[]
    for kind in KINDS:
        b=base(kind);w=b['weights'];r=b['residual_degree'];best={};count=anchors=0
        for p in bell_partitions(len(w)):
            ds=[sum(w[i] for i in g) for g in p]
            answers=[2*max([r]+ds)]
            answers += [d+2*max([r]+[v for j,v in enumerate(ds) if j!=i]) for i,d in enumerate(ds)]
            k=len(p);best[k]=min(best.get(k,float('inf')),min(answers));count+=1;anchors+=len(answers)
        assert best=={len(p['partition']):p['exact_degree'] for p in search(kind)['best_by_group_count']}
        floor=2*max([r]+w);attained=min(best.values());assert floor==attained
        # For these specific positive weight lists every anchored plan has
        # at least the largest factor plus the needed other positive mass;
        # exhaust all distinguished subsets to certify the unlimited floor.
        for mask in range(1,1<<len(w)):
            A=sum(v for i,v in enumerate(w) if mask>>i&1)
            other=max([r]+[v for i,v in enumerate(w) if not mask>>i&1])
            assert A+2*other>=floor
        records.append(dict(kind=kind,bell_partitions=count,objective_choices=anchors,
                            independently_optimal_degrees=best,family_floor=attained,
                            distinguished_subsets=(1<<len(w))-1))
    return records


def algebra_audit(cases=24):
    rng=random.Random(879564);counts=Counter()
    for kind in KINDS:
      b=base(kind)
      for choice in search(kind)['best_by_group_count']:
        p=grouped(b,choice['partition'],choice['anchor']);rows,out=polynomial_source(p)
        for case in range(cases):
            signed=case>=cases//2
            values={n:rng.randrange(-4,5) if signed else rng.randrange(1,5) for n in parent.RETAINED+['x']}
            B=(16,32,64,256)[case%4]
            fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=B.bit_length()-1,inner_bits=3)
            e=parent.run(rows,values,fixed)
            before=parent.run(parent.source(kind=='normalized_units'),values,fixed)
            lifted=parent.run(parent.parent(kind=='normalized_units').sources()[3],parent.to_parent(values,B),fixed)
            assert all(e[n]==before[n]==lifted[n] for n,_,_,_ in b['source'])
            gs=[prod(before[b['factors'][i]] for i in g) for g in p['partition']]
            assert gs==[e[n] for n in p['group_products']]
            get=lambda a:before[a] if isinstance(a,str) else a
            R=sum((get(a)-get(bb))**2 for a,bb in b['ordinary_comparisons'])
            if kind=='ordinary_comparison':
                assert before['norm_strong']==1+get('ic22')-get('R16')
            anchor=p['anchor'];R+=sum((v-1)**2 for j,v in enumerate(gs) if j!=anchor)
            expected=R if anchor is None else gs[anchor]*(1+R)-1
            assert e[out]==expected
            counts['complete_register_and_manual_output_identities']+=1
            counts['signed_identities']+=signed
    return dict(counts)


def degree_audit():
    z=sp.Symbol('z');records=[]
    for choice in frontier():
        p=build(choice['operations']);rows,out=polynomial_source(p)
        for B,offset in ((32,1),(128,2)):
            scales={n:1+(i+offset)%4 for i,n in enumerate(parent.RETAINED+['x'])}
            scales.update(tau_gap=5,eta=1,zeta=2,Jrep=2,x=1)
            values={n:sp.Poly(scales[n]*z+i+1,z) for i,n in enumerate(parent.RETAINED+['x'])}
            fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=B.bit_length()-1,inner_bits=3)
            e=parent.run(rows,values,fixed)
            assert [e[f].degree() for f in p['factors']]==p['weights']
            assert [e[g].degree() for g in p['group_products']]==exact_degree(p)['group_degrees']
            assert e[out].degree()==choice['exact_degree']
            records.append(dict(operations=choice['operations'],B=B,exact_degree=e[out].degree(),
                                leading_coefficient=str(e[out].LC())))
    return records


def guard_audit():
    rejected=0
    for kind in KINDS:
        b=base(kind);n=len(b['factors']);p=grouped(b,[list(range(n))],0)
        bad=[dict(b,source=b['source'][:-1]),dict(b,weights=[1]*n),dict(b,ordinary_comparisons=[] if b['ordinary_comparisons'] else [('q',1)])]
        for v in bad:
            try:grouped(v,[list(range(n))],0)
            except AssertionError:rejected+=1
            else:raise AssertionError('noncanonical base accepted')
        for part,anchor in [([[0],[0]+list(range(1,n))],None),([list(range(n-1))],0),([list(range(n))],True),([list(range(n))],2)]:
            try:grouped(b,part,anchor)
            except AssertionError:rejected+=1
            else:raise AssertionError('invalid plan accepted')
        for key,val in [('source',p['source'][:-1]),('weights',[1]*n),('group_products',['q'])]:
            try:polynomial_source(dict(p,**{key:val}))
            except AssertionError:rejected+=1
            else:raise AssertionError('modified packet accepted')
    return rejected


def verify():
    searches=[search(k) for k in KINDS];fr=frontier();emitted=[]
    for r in fr:
        p=build(r['operations']);rows,out=polynomial_source(p)
        emitted.append(dict(record(p),source=rows,output=out,
                            source_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest()))
    return dict(status='PASS_COMPLETE75_ASYMMETRIC_FACTOR_PARTITIONS',
        searches=searches,frontier=fr,emitted=emitted,independent_objectives=independent_objectives(),
        source_audit=algebra_audit(),exact_degree_audit=degree_audit(),rejected_callers=guard_audit(),
        scope='Exact finite disjoint-factor grouping and optional single-anchor family for three guarded asymmetric87/88 bases. Same supplied positive zeros within each base; only accepted-input equivalence across strong treatments. Exact degrees from nonzero leading forms; no all-circuit or universal minimal-degree claim. Separate75 certificate unchanged.')


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print([(r['operations'],r['exact_degree']) for r in result['frontier']]);print(result['source_audit'])
