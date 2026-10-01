"""Transport the complete four-base U21 partitions through repunit376.

Every plan saves two total operations (+2M,-4A), with identical integer
polynomials, supplied domains and propagated degree dictionaries.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_selector_reuse_partitions as parent
engine=parent.parent
import korec_packed_repunit376 as reuse

core=parent.core
execute=parent.execute
polynomial_source=parent.polynomial_source
degree_bound=parent.degree_bound
record=parent.record


@lru_cache(None)
def base(normalized=True,scaled=True,program_radix=False):
    old=parent.base(normalized,scaled,program_radix)
    rows=reuse.rewrite_rows(old)
    roots=old['unit_factors']+[x for pair in old['ordinary_comparisons'] for x in pair]
    factors=engine.closure(rows,roots)
    scaffold=dict(old,factor_source=factors,repunit_partition_parent=old,
        counter_repunit_partitions=True,
        finite_family_identity='Every plan has the same integer polynomial and supplied coordinates as its corresponding four-base parent; exactly two operations are removed, with two more multiplications and four fewer additions.')
    result=engine.grouped(scaffold,[list(range(len(old['unit_factors'])))],0)
    assert degree_bound(result)==degree_bound(old)
    assert len(result['factor_source'])==len(old['factor_source'])-2
    return result


def regroup(original,partition,anchor):
    assert original==base(original['counter_strong_normalized'],original['counter_scale_projected'],original['counter_program_radix']),'complete canonical repunit partition base required'
    return engine.grouped(original,partition,anchor)


def compare_ledgers(new,old):
    a,b=record(new),record(old)
    assert a['degree']==b['degree']
    assert new['parameters']==old['parameters'] and new['auxiliaries']==old['auxiliaries']
    assert new['comparisons']==old['comparisons'] and new['unit_factors']==old['unit_factors']
    assert new['interfaces']==old['interfaces']
    for key in ('certificate','polynomial'):
        assert a[key]['operations']==b[key]['operations']-2
        assert a[key]['additions_subtractions']==b[key]['additions_subtractions']-4
        assert a[key]['multiplications']==b[key]['multiplications']+2
    assert a['certificate']['witnesses']==b['certificate']['witnesses']
    assert a['certificate']['equations']==b['certificate']['equations']
    return a


@lru_cache(None)
def search(normalized,scaled,program_radix):
    prior=parent.search(normalized,scaled,program_radix);old=parent.base(normalized,scaled,program_radix)
    current=base(normalized,scaled,program_radix);records=[]
    for plan in prior['best_by_group_count']:
        p,a=plan['partition'],plan['anchor']
        records.append(compare_ledgers(regroup(current,p,a),parent.regroup(old,p,a)))
    return dict(prior,best_by_group_count=records,
        optimizer_provenance='Exact finite parent search transported through an all-plan constant cost shift and identical propagated objective.')


@lru_cache(None)
def frontier(program_radix=False,witnesses=None):
    assert witnesses in (None,50,51)
    rows=[r for n in (False,True) for s in (False,True) if witnesses is None or (50 if s else 51)==witnesses
          for r in search(n,s,program_radix)['best_by_group_count']]
    rows.sort(key=lambda r:(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']))
    result=[];best=float('inf')
    for r in rows:
        if r['polynomial']['degree_upper_bound']<best:result.append(r);best=r['polynomial']['degree_upper_bound']
    assert [(r['polynomial']['operations']+2,r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in result]==[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in parent.frontier(program_radix,witnesses)]
    return result


def build(operations=None,*,program_radix=False,witnesses=None):
    plans=frontier(program_radix,witnesses)
    plan=plans[0] if operations is None else next(r for r in plans if r['polynomial']['operations']==operations)
    return regroup(base(plan['normalized'],plan['scaled'],program_radix),plan['partition'],plan['anchor'])


def source_audit(original,partition,anchor,seed,cases=8):
    new=regroup(original,partition,anchor)
    old=parent.regroup(original['repunit_partition_parent'],partition,anchor)
    ns,no=polynomial_source(new);os,oo=polynomial_source(old)
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        values={n:draw() for n in new['parameters']+new['auxiliaries']}
        a,b=execute(ns,values),execute(os,values)
        assert all(a[n]==b[n] for n,_,_,_ in os if n not in reuse.DELETED)
        restored=reuse.restore_registers(a)
        assert all(restored[n]==b[n] for n in reuse.DELETED)
        assert a[no]==b[oo]
        counts['complete_retained_register_and_output_identities']+=1
        counts['signed_identity_assignments']+=signed
    return dict(counts)


def finalizer_audit(original,partition,anchor,seed,cases=8):
    packet=regroup(original,partition,anchor);ss,out=polynomial_source(packet)
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        before=execute(original['factor_source'],values);e=execute(ss,values)
        at=lambda x:before[x] if isinstance(x,str) else x
        products=[]
        for group in partition:
            value=1
            for i in group:value*=before[original['unit_factors'][i]]
            products.append(value)
        assert products==[e[n] for n in packet['group_products']]
        expected=sum((at(a)-at(b))**2 for a,b in original['ordinary_comparisons'])
        expected+=sum((x-1)**2 for j,x in enumerate(products) if j!=anchor)
        if anchor is not None:expected=products[anchor]*(1+expected)-1
        assert e[out]==expected
        counts['manual_group_and_finalizer_outputs']+=1
        counts['signed_manual_assignments']+=signed
    return dict(counts)


def guards():
    p=base();nf=len(p['unit_factors']);bad=[dict(p,parameters=['changed']),dict(p,source=p['source'][:-1]),dict(p,interfaces={'hidden':'native__bound_beta'}),parent.base()]
    for v in bad:
        try:regroup(v,[list(range(nf))],0)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('altered or preceding base accepted')
    return len(bad)


def verify():
    studies=[];bases=[];selected=[];totals=Counter();frontiers={};floors={}
    for pr in (False,True):
      for n in (False,True):
       for s in (False,True):
        p=base(n,s,pr);study=search(n,s,pr);studies.append(study)
        rec=compare_ledgers(p,parent.base(n,s,pr));nf=len(p['unit_factors'])
        rec['base_identity_audit']=source_audit(p,[list(range(nf))],0,376100+len(bases));bases.append(rec)
        totals.update(rec['base_identity_audit'])
        totals.update(finalizer_audit(p,[list(range(nf))],0,376200+len(bases)))
        groups=[list(range(j,nf,3)) for j in range(3)]
        for anchor in (None,1):
            compare_ledgers(regroup(p,groups,anchor),parent.regroup(parent.base(n,s,pr),groups,anchor))
            totals.update(source_audit(p,groups,anchor,376300+len(bases)))
            totals.update(finalizer_audit(p,groups,anchor,376500+len(bases)))
      for witnesses in (None,50,51):
        plans=frontier(pr,witnesses)
        frontiers[f'{pr}/{witnesses}']=[(r['polynomial']['operations'],r['polynomial']['degree_upper_bound'],r['certificate']['witnesses']) for r in plans]
        lower=min(st['floor_certificate']['lower_bound'] for st in studies if st['program_radix']==pr and (witnesses is None or (50 if st['scaled'] else 51)==witnesses))
        assert plans[-1]['polynomial']['degree_upper_bound']==lower
        floors[f'{pr}/{witnesses}']=dict(lower_bound=lower,attained_operations=plans[-1]['polynomial']['operations'])
      seen=set()
      for witnesses in (None,50,51):
       for r in frontier(pr,witnesses):
        key=(r['normalized'],r['scaled'],tuple(map(tuple,r['partition'])),r['anchor'])
        if key in seen:continue
        seen.add(key);p=base(key[0],key[1],pr);packet=regroup(p,r['partition'],r['anchor']);ss,out=polynomial_source(packet);rec=record(packet)
        rec['identity_audit']=source_audit(p,r['partition'],r['anchor'],376700+len(selected));totals.update(rec['identity_audit'])
        rec['manual_finalizer_audit']=finalizer_audit(p,r['partition'],r['anchor'],376900+len(selected));totals.update(rec['manual_finalizer_audit'])
        rec.update(source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest());selected.append(rec)
    assert frontiers['False/None']==[(376,21549,50),(378,18951,50),(380,13456,50),(381,9114,51),(383,6512,51),(385,4542,51),(387,3896,51)]
    return dict(status='PASS_KOREC_PACKED_REPUNIT_PARTITIONS',studies=studies,bases=bases,
        frontiers=frontiers,attained_floor_certificates=floors,selected_sources=selected,audit_totals=dict(totals),rejected_callers=guards(),
        scope='Every finite four-base partition source saves exactly two operations (+2M,-4A) and keeps its same integer polynomial, coordinates and guarded degree dictionary. Parent exact finite optima transport uniformly; no new exact-degree or unrestricted circuit lower bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['frontiers']);print(result['audit_totals'])
