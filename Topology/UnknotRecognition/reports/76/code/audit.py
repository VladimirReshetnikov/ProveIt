"""Deterministic independent finite audits; writes evidence only on request."""
from __future__ import annotations
import argparse
import itertools
import json
import platform
import random
import time
from pathlib import Path
from disk_algebra import *
from compressed_search import *
from checker import check, independent_feature, independent_compose, independent_disk_cap
from mesh_oracle import replay_pair, replay_word
from star_search import star_summary


def opt(table, cap, charge):
    return min((x.cost for x in table if x.charge == charge and independent_disk_cap(x.partition,cap)), default=None)


def enumerate_source(source):
    """Independent original-syntax semantics; no power-lowering compiler."""
    languages=[]
    for n,node in enumerate(source['nodes']):
        kind=node['kind']
        if kind=='identity':words=[()]
        elif kind=='atoms':words=[((n,i),) for i in range(len(node['options']))]
        elif kind=='concat':words=[a+b for a in languages[node['left']] for b in languages[node['right']]]
        elif kind=='union':words=[w for child in node['children'] for w in languages[child]]
        elif kind=='power':
            words=[()]
            for _ in range(int(node['exponent'])):
                words=[a+b for a in words for b in languages[node['base']]]
        else:raise AssertionError(kind)
        languages.append(words)
    return languages[source.get('root',len(languages)-1)]


def make_options(b,count,q,rng):
    ps=list(partitions(2*b))
    return [{'partition':list(rng.choice(ps)),'cost':rng.randrange(-6,10),'charge':rng.randrange(q)} for _ in range(count)]


def run():
    start=time.perf_counter();rng=random.Random(2026100917)
    count={}
    num=0;ranks=[]
    for r in range(1,7):
        ps=list(partitions(r));rows=[]
        for p in ps:
            assert feature(p)==independent_feature(p)
            row=0
            for i,q in enumerate(ps):
                x=cap_pairing(p,q)
                assert x==independent_disk_cap(p,q)
                row|=x<<i;num+=1
            rows.append(row)
        rank=binary_rank(rows);assert rank==1<<(r-1)
        ranks.append({'ports':r,'partitions':len(ps),'rank':rank})
    count['exhaustive_cap_entries']=num;count['rank_table']=ranks
    num=0
    for a,b,c in itertools.product(range(1,4),repeat=3):
        ps=list(partitions(a+b));qs=list(partitions(b+c))
        pairs=itertools.product(ps,qs) if a+b+c<=6 else ((rng.choice(ps),rng.choice(qs)) for _ in range(200))
        for p,q in pairs:
            x,y=Morphism(a,b,p),Morphism(b,c,q)
            z=compose(x,y)
            assert (None if z is None else z.partition)==independent_compose(p,q,a,b,c)
            expected=matrix(z) if z else tuple((0,)*(1<<(a-1)) for _ in range(1<<(c-1)))
            assert matrix_product(matrix(y),matrix(x))==expected
            num+=1
    count['rectangular_matrix_products']=num
    num=0
    for b in range(1,4):
        ps=list(partitions(2*b))
        for p,q in itertools.product(ps,repeat=2):
            lhs=matrix_trace_epsilon(matrix_product(matrix(flip(Morphism(b,b,q))),matrix(Morphism(b,b,p))))
            assert lhs==independent_disk_cap(p,q);num+=1
    count['trace_pairings']=num
    n=0
    for _ in range(1200):
        b=rng.choice([1,2,3]);q=rng.choice([1,2,4]);ps=list(partitions(2*b))
        source=[Candidate(rng.choice(ps),rng.randrange(-100,101),rng.randrange(q),()) for _ in range(rng.randrange(1,80))]
        reduced=[source[i] for i in reduce_family(source)]
        for _ in range(12):
            cap=rng.choice(ps);charge=rng.randrange(q)
            assert opt(source,cap,charge)==opt(reduced,cap,charge);n+=1
    count['weighted_families']=1200;count['weighted_queries']=n
    num=0
    for _ in range(250):
        b=rng.choice([1,2,3]);q=rng.choice([1,2,4]);w=rng.randrange(9)
        source=repeated_source(b,make_options(b,rng.randrange(1,8),q,rng),w,q)
        result=solve(source);checked=check(source,result.certificate())
        assert result.tables==checked.tables
        exact=sequential(source,w,exact=True)
        for cap in partitions(2*b):
            for h in range(q):
                assert opt(result.tables[result.program.root],cap,h)==opt(exact,cap,h);num+=1
    count['powered_vs_explicit_languages']=250;count['powered_vs_explicit_cap_queries']=num
    num=0
    for r in range(1,5):
        for p,q in itertools.product(partitions(r),repeat=2):
            assert replay_pair(p,q)['is_single_disk']==independent_disk_cap(p,q);num+=1
    for _ in range(600):
        r=rng.choice([5,6]);ps=list(partitions(r));p,q=rng.choices(ps,k=2)
        assert replay_pair(p,q)['is_single_disk']==independent_disk_cap(p,q);num+=1
    count['literal_pair_meshes']=num
    assignments=0;found=0
    for case in range(80):
        b=rng.choice([1,2]);q=rng.choice([1,2,4]);m=rng.randrange(1,4);w=rng.randrange(1,5)
        source=repeated_source(b,make_options(b,m,q,rng),w,q)
        if case%3==0:
            # (A union B)^W, with equal unit spans and different libraries.
            source['nodes']=[source['nodes'][0],{'kind':'atoms','options':make_options(b,1,q,rng)},
                             {'kind':'union','children':[0,1]}, {'kind':'power','base':2,'exponent':str(w)}]
        cap=rng.choice(list(partitions(2*b)));h=rng.randrange(q)
        best=None
        for word in enumerate_source(source):
            options=[source['nodes'][n]['options'][i] for n,i in word]
            parts=[tuple(op['partition']) for op in options]
            charge=0
            for op in options:charge^=op['charge']
            cost=sum(op['cost'] for op in options)
            mesh=replay_word(b,parts,cap);assignments+=1
            if mesh['is_single_disk'] and charge==h:
                found+=1;best=cost if best is None else min(best,cost)
        result=solve(source);assert result.query(cap,[h])['cost']==best
        assert check(source,result.certificate()).tables==result.tables
    count['literal_complete_languages']=80;count['literal_word_meshes']=assignments;count['feasible_word_assignments']=found
    # One huge, analytically solvable independent-choice example.
    W=2**1024
    source=repeated_source(1,[{'partition':[0,0],'cost':1,'charge':0},
                             {'partition':[0,0],'cost':-3,'charge':1}],W,2)
    t=time.perf_counter();result=solve(source);solve_seconds=time.perf_counter()-t
    answer=result.query((0,1),[1]);assert answer['cost']==-3*W+4
    t=time.perf_counter();checked=check(source,result.certificate());check_seconds=time.perf_counter()-t
    assert checked.tables==result.tables
    stats=result.witness_statistics(answer['witness'])
    assert stats['expanded_length']==W
    huge={'exponent':'2^1024','optimum_formula':'-3*2^1024+4','solve_seconds':solve_seconds,
          'check_seconds':check_seconds,'compiled_rules':len(result.program.rules),
          'retained_total':result.metrics['retained_total'],'composition_pairs':result.metrics['composition_pairs'],
          'reachable_witness_nodes':stats['reachable_dag_nodes'],
          'certificate_bytes':len(json.dumps(result.certificate(),separators=(',',':')).encode())}
    # Free-star pumping oracle, all words up to the proved bound for width one.
    for _ in range(150):
        opts=[{'partition':list(p),'cost':rng.randrange(9),'charge':rng.randrange(4)} for p in partitions(2)]
        s={'width':1,'charges':4,'nodes':[{'kind':'atoms','options':opts}]}
        rows,stats=star_summary(s)
        allrows=[]
        for w in range(8):allrows.extend(sequential(s,w,exact=True))
        assert stats['max_word_length']<8
        for cap in partitions(2):
            for h in range(4):assert opt(rows,cap,h)==opt(allrows,cap,h)
    count['free_star_languages']=150
    return {'seed':2026100917,'status':'PASS','environment':{'python':platform.python_version(),'platform':platform.platform()},
            'counts':count,'huge_repetition':huge,'elapsed_seconds':time.perf_counter()-start}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    out=run();text=json.dumps(out,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    else:print(text,end='')

if __name__=='__main__':main()
