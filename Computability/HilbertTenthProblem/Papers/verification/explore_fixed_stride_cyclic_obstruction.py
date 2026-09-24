#!/usr/bin/env python3
"""Exact finite-state obstruction for cyclic local words with two markers.

No arithmetic certificate is modified or priced. Default replays the receipt.
"""
from itertools import product
from pathlib import Path
import argparse
import json
import random


def graph(alphabet, offsets, allowed, start=frozenset({0}), end=frozenset({1})):
    offsets=tuple(offsets)
    assert offsets and 0 in offsets and not start & end
    lo,hi=min(offsets),max(offsets);span=hi-lo
    vertices=list(product(alphabet,repeat=span))
    index={word:i for i,word in enumerate(vertices)}
    edges=[]
    for block in product(alphabet,repeat=span+1):
        if tuple(block[d-lo] for d in offsets) not in allowed:continue
        u=index[block[:-1]];v=index[block[1:]];label=block[-lo]
        kind='S' if label in start else 'E' if label in end else 'O'
        edges.append((u,v,label,kind))
    return vertices,edges


def ordinary_matrix(n,edges):
    rows=[0]*n
    for u,v,_,kind in edges:
        if kind=='O':rows[u]|=1<<v
    return tuple(rows)


def multiply(left,right):
    result=[]
    for row in left:
        out=0
        while row:
            bit=row & -row;row-=bit;out|=right[bit.bit_length()-1]
        result.append(out)
    return tuple(result)


def identity(n):return tuple(1<<i for i in range(n))


def power(A,n):
    result=identity(len(A))
    while n:
        if n&1:result=multiply(result,A)
        A=multiply(A,A);n//=2
    return result


def closure(A):
    rows=[row|(1<<i) for i,row in enumerate(A)]
    for k in range(len(A)):
        for i in range(len(A)):
            if rows[i]>>k&1:rows[i]|=rows[k]
    return tuple(rows)


def target_pairs(n,edges,tail_min=0):
    assert tail_min>=0
    A=ordinary_matrix(n,edges)
    reach=multiply(power(A,tail_min),closure(A));pairs=[0]*n
    for u,v,_,kind in edges:
        if kind!='S':continue
        for w,z,_,other in edges:
            if other=='E' and reach[z]>>u&1:pairs[v]|=1<<w
    return A,tuple(pairs)


def accepts(A,pairs,x):
    assert x>=1
    return any(row & target for row,target in zip(power(A,x-1),pairs))


def direct_valid(word,offsets,allowed):
    n=len(word)
    return all(tuple(word[(i+d)%n] for d in offsets) in allowed for i in range(n))


def closed_label_word(word,vertices,edges,offsets):
    """Construct the exact graph walk, including all wrap coincidences."""
    lo,hi=min(offsets),max(offsets);n=len(word)
    index={v:i for i,v in enumerate(vertices)}
    edge_set={(u,v,label) for u,v,label,_ in edges}
    walk=[]
    for i in range(n):
        block=tuple(word[(i+j)%n] for j in range(lo,hi+1))
        edge=(index[block[:-1]],index[block[1:]],word[i])
        if edge not in edge_set:return None
        walk.append(edge)
    assert all(walk[i][1]==walk[(i+1)%n][0] for i in range(n))
    return walk


def brute_marked(alphabet,offsets,allowed,x,V,start=(0,),end=(1,),minimum_length=1):
    ordinary=tuple(s for s in alphabet if s not in start and s not in end)
    tail_min=max(0,minimum_length-x-1)
    for n in range(max(x+1,minimum_length),x+tail_min+V+1):
        for s,e in product(start,end):
            for rest in product(ordinary,repeat=n-2):
                word=[];it=iter(rest)
                for i in range(n):word.append(s if i==0 else e if i==x else next(it))
                if direct_valid(word,offsets,allowed):return n
    return None


def eventual_period(A,pairs):
    seen={};values=[];current=identity(len(A))
    while current not in seen:
        seen[current]=len(values)
        values.append(any(row & target for row,target in zip(current,pairs)))
        current=multiply(current,A)
    first=seen[current];period=len(values)-first
    assert period>0
    for x in range(first+1,first+1+4*period):
        assert accepts(A,pairs,x)==accepts(A,pairs,x+period)
    return dict(first_periodic_input=first+1,period=period,
                prefix_and_one_period=values)


def verify():
    rng=random.Random(770076)
    graph_cases=short_cases=walk_cases=marked_cases=positive=negative=0
    period_records=[]
    # Full word/closed-walk comparison: both signs of offsets and span zero.
    for offsets in ((0,),(0,-1),(0,-1,-3),(-2,0,2),(0,1,4)):
        alphabet=(0,1)
        universe=list(product(alphabet,repeat=len(offsets)))
        for trial in range(8):
            allowed=set(universe) if trial==0 else set() if trial==1 else {
                t for t in universe if rng.randrange(2)}
            vertices,edges=graph(alphabet,offsets,allowed)
            for n in range(1,7):
                for word in product(alphabet,repeat=n):
                    assert direct_valid(word,offsets,allowed)==(
                        closed_label_word(word,vertices,edges,offsets) is not None)
                    walk_cases+=1
                    short_cases+=int(n<max(offsets)-min(offsets))
            graph_cases+=1
    # With one ordinary symbol, the complete x+V bound stays cheap even
    # for span 3; all actual cyclic lengths in this bound are enumerated.
    for alphabet,offsets,trials in (
            ((0,1,2),(0,),10),
            ((0,1,2),(0,-1),24),
            ((0,1,2),(0,-1,-2),24),
            ((0,1,2),(0,-1,-3),12),
            ((0,1,2,3),(0,-1),24)):
        universe=list(product(alphabet,repeat=len(offsets)))
        for trial in range(trials):
            allowed=set(universe) if trial==0 else set() if trial==1 else {
                t for t in universe if rng.randrange(4)!=0}
            vertices,edges=graph(alphabet,offsets,allowed)
            A,pairs=target_pairs(len(vertices),edges)
            for x in range(1,6):
                actual=accepts(A,pairs,x)
                witness=brute_marked(alphabet,offsets,allowed,x,len(vertices))
                assert actual==(witness is not None)
                if witness is not None:assert x+1<=witness<=x+len(vertices)
                marked_cases+=1;positive+=actual;negative+=not actual
            result=eventual_period(A,pairs)
            period_records.append(dict(alphabet=len(alphabet),offsets=list(offsets),
                                       vertices=len(vertices),trial=trial,**result))
    # A genuinely periodic marked-distance language: S,a,(b,a)*,E,S.
    # Relation is (center,previous), symbols S=0,E=1,a=2,b=3.
    alphabet=(0,1,2,3);offsets=(0,-1)
    allowed={(2,0),(3,2),(2,3),(1,2),(0,1)}
    vertices,edges=graph(alphabet,offsets,allowed)
    A,pairs=target_pairs(len(vertices),edges)
    even_example=[]
    for x in range(1,65):
        result=accepts(A,pairs,x);assert result==(x%2==0)
        even_example.append(result)
    even_period=eventual_period(A,pairs)
    # Input-computable negative/positive strides; fixed table throughout.
    variable_cases=0
    alphabet=(0,1,2)
    allowed={t for t in product(alphabet,repeat=3) if t[0]!=t[1] or t[2]==2}
    for family in ('bounded','growing','mixed_sign'):
        for x in range(1,5):
            h=x%3+1 if family=='bounded' else x if family=='growing' else -x
            offsets=(0,-1,-h)
            vertices,edges=graph(alphabet,offsets,allowed)
            A,pairs=target_pairs(len(vertices),edges)
            assert accepts(A,pairs,x)==(brute_marked(alphabet,offsets,allowed,x,len(vertices)) is not None)
            variable_cases+=1
    bounded_choice_cases=0
    for x in range(1,5):
        graph_results=[];direct_results=[]
        for h in range(1,x+2):
            offsets=(0,-1,-h)
            vertices,edges=graph(alphabet,offsets,allowed)
            A,pairs=target_pairs(len(vertices),edges)
            graph_results.append(accepts(A,pairs,x))
            direct_results.append(brute_marked(alphabet,offsets,allowed,x,len(vertices)) is not None)
            bounded_choice_cases+=1
        assert graph_results==direct_results and any(graph_results)==any(direct_results)
    minimum_cases=minimum_positive=minimum_negative=0
    for h in (1,2,3):
        offsets=(0,-1,-h)
        universe=set(product(alphabet,repeat=3))
        relations=(universe,set(),allowed,{t for t in universe if t[0]!=t[1]})
        for relation in relations:
            vertices,edges=graph(alphabet,offsets,relation)
            for x in range(1,5):
                for minimum in (1,9,h+1,x*x+2):
                    tail_min=max(0,minimum-x-1)
                    A,pairs=target_pairs(len(vertices),edges,tail_min)
                    result=accepts(A,pairs,x)
                    witness=brute_marked(alphabet,offsets,relation,x,len(vertices),minimum_length=minimum)
                    assert result==(witness is not None)
                    if witness is not None:
                        assert max(x+1,minimum)<=witness<=x+tail_min+len(vertices)
                    minimum_cases+=1;minimum_positive+=result;minimum_negative+=not result
    return dict(status='PASS_FIXED_STRIDE_CYCLIC_OBSTRUCTION',
                graph_relations=graph_cases,word_closed_walk_comparisons=walk_cases,
                short_cycle_comparisons=short_cases,complete_bound_marker_cases=marked_cases,
                accepted_marker_cases=positive,rejected_marker_cases=negative,
                periodicity_records=period_records,even_distance_example=even_period,
                checked_even_distance_inputs=len(even_example),
                input_computable_stride_cases=variable_cases,
                bounded_existential_stride_graphs=bounded_choice_cases,
                computable_minimum_length_cases=minimum_cases,
                minimum_length_acceptances=minimum_positive,minimum_length_rejections=minimum_negative,
                scope='Finite local cyclic languages with exactly two unique marker predicates; no additional unbounded nonlocal arithmetic constraints',
                proof='../1980/EXPLORATION_FIXED_STRIDE_CYCLIC_OBSTRUCTION.md',
                operation_count_claim=None,
                review='Author and independent complete proof/source reviews pass; scoped representation obstruction, not an arithmetic lower bound')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print({key:value for key,value in result.items() if key!='periodicity_records'})
