#!/usr/bin/env python3
"""Exact finite checks for 'Filter Profiles and Open-Query Complexity'.

Python standard library only. Infinite filters and spaces are NOT simulated.
The finite graph, word, extremal, and capacity statements are checked by
independent exhaustive routines. Run without -O (assertions are checks).
"""
from __future__ import annotations
import argparse
import csv
import itertools as it
import json
from pathlib import Path
from typing import Iterable


def arcs(q: int) -> list[tuple[int, int]]:
    return [(u, v) for u in range(q) for v in range(q) if u != v]


def rows(q: int, mask: int) -> list[int]:
    out = [0] * q
    for j, (u, v) in enumerate(arcs(q)):
        if mask >> j & 1:
            out[u] |= 1 << v
    return out


def topo(out: list[int], subset: int) -> list[int] | None:
    """Kahn-style source deletion, with independently computed incoming arcs."""
    order: list[int] = []
    while subset:
        candidates = [v for v in range(len(out)) if subset >> v & 1
                      and not any((subset >> u & 1) and (out[u] >> v & 1)
                                  for u in range(len(out)))]
        if not candidates:
            return None
        v = candidates[0]
        order.append(v)
        subset ^= 1 << v
    return order


def min_fvs(q: int, mask: int) -> tuple[int, list[int], list[int]]:
    out = rows(q, mask)
    for k in range(q):
        for rem in it.combinations(range(q), k):
            subset = ((1 << q) - 1) ^ sum(1 << v for v in rem)
            order = topo(out, subset)
            if order is not None:
                return k, list(rem), order
    raise AssertionError('A one-vertex digraph is acyclic.')


def word_mask(q: int, w: tuple[int, ...] | list[int]) -> tuple[int, int]:
    index = {e: i for i, e in enumerate(arcs(q))}
    seen = 0
    covered = 0
    for v in w:
        for u in range(q):
            if u != v and seen >> u & 1:
                covered |= 1 << index[u, v]
        seen |= 1 << v
    return seen, covered


def words(q: int, length: int) -> Iterable[tuple[int, ...]]:
    if length == 0:
        yield ()
    else:
        for w in it.product(range(q), repeat=length):
            if all(w[j] != w[j+1] for j in range(length-1)):
                yield w


def word_optima(q: int) -> tuple[list[int], int]:
    """Enumerate words, then a supermask-min transform; no FVS calls."""
    bits = q*(q-1)
    best = [10**9] * (1 << bits)
    count = 0
    for length in range(1, 2*q):
        for w in words(q, length):
            count += 1
            seen, mask = word_mask(q, w)
            if seen == (1 << q) - 1:
                best[mask] = min(best[mask], length)
    for bit in range(bits):
        for mask in range(1 << bits):
            if not mask >> bit & 1:
                best[mask] = min(best[mask], best[mask | (1 << bit)])
    return best, count


def threshold(q: int, r: int) -> int:
    if not 1 <= r <= q:
        raise ValueError('Require 1 <= r <= q.')
    a, s = divmod(q, r)
    return r*a*(a-1) + 2*a*s


def balanced_cliques(q: int, r: int) -> int:
    a, s = divmod(q, r)
    groups: list[list[int]] = []
    start = 0
    for size in [a+1]*s + [a]*(r-s):
        groups.append(list(range(start, start+size)))
        start += size
    edge_set = {(u,v) for group in groups for u in group for v in group if u != v}
    return sum(1 << j for j,e in enumerate(arcs(q)) if e in edge_set)


def is_balanced_cluster(q: int, mask: int, r: int) -> bool:
    """Direct structural test, independent of degrees-only equality tests."""
    out = rows(q, mask)
    for u in range(q):
        for v in range(q):
            if bool(out[u] >> v & 1) != bool(out[v] >> u & 1):
                return False
    remaining = set(range(q)); sizes = []
    while remaining:
        u = min(remaining)
        group = {u} | {v for v in remaining if out[u] >> v & 1}
        for v in group:
            if out[v] != sum(1 << w for w in group if w != v):
                return False
        sizes.append(len(group)); remaining -= group
    return len(sizes) == r and max(sizes)-min(sizes) <= 1


def graph_checks(max_q: int) -> tuple[list[dict], list[dict], dict[int,list[int]]]:
    summary=[]; extrema=[]; tau_cache={}
    for q in range(1,max_q+1):
        best, word_count = word_optima(q)
        taus=[]
        min_edges=[10**9]*(q+1)
        eq_counts=[0]*(q+1)
        for mask in range(1 << (q*(q-1))):
            k, rem, order = min_fvs(q,mask)
            taus.append(k)
            assert best[mask] == q+k, (q,mask,best[mask],k)
            witness=rem+order+list(reversed(rem))
            seen, cover=word_mask(q,witness)
            assert seen==(1<<q)-1 and cover & mask == mask
            assert len(witness)==q+k
            alpha=q-k
            m=mask.bit_count()
            for r in range(alpha,q+1):
                min_edges[r]=min(min_edges[r],m)
                assert m >= threshold(q,r)
                if m == threshold(q,r):
                    assert is_balanced_cluster(q,mask,r)
                    eq_counts[r]+=1
        for r in range(1,q+1):
            assert min_edges[r]==threshold(q,r)
            extrema.append(dict(q=q,r=r,min_arcs=min_edges[r],equality_graphs=eq_counts[r]))
        summary.append(dict(q=q,graphs=len(taus),reduced_words=word_count,
                            word_fvs_checks=len(taus)))
        tau_cache[q]=taus
    return summary,extrema,tau_cache


def star_options(q: int, capacity: int) -> list[tuple[int,int]]:
    index={e:j for j,e in enumerate(arcs(q))}
    opts=[]
    for center in range(q):
        others=[v for v in range(q) if v != center]
        for size in range(min(capacity,q-1)+1):
            for targets in it.combinations(others,size):
                mask=sum(1 << index[center,v] for v in targets)
                opts.append((mask,1<<center))
    return opts


def feasible_bins(capacities: tuple[int,...], s: int) -> bool:
    # Direct enumeration of assignments, not a graph test.
    for assignment in it.product(range(s),repeat=len(capacities)):
        if len(set(assignment)) != s:
            continue
        totals=[0]*s
        for i,b in enumerate(assignment):
            totals[b]+=capacities[i]
        if min(totals)>=s-1:
            return True
    return False


def capacity_checks(tau_cache: dict[int,list[int]]) -> list[dict]:
    records=[]
    for q,max_t in [(3,5),(4,3)]:
        if q not in tau_cache:
            continue
        for t in range(1,max_t+1):
            for cap in it.combinations_with_replacement(range(1,q),t):
                states={(0,0)}
                for b in cap:
                    states={(g|star,centers|center)
                            for g,centers in states for star,center in star_options(q,b)}
                for s in range(1,min(q,t)+1):
                    maximum=max(q+tau_cache[q][g]
                                for g,centers in states if centers.bit_count()==s)
                    bins=feasible_bins(cap,s)
                    assert (maximum==q+s-1)==bins, (q,cap,s,maximum,bins)
                    records.append(dict(q=q,capacities=list(cap),top_colors=s,
                                        max_layers=maximum,attains_bound=bins))
    return records


def positive_cell_checks() -> int:
    count=0
    for q in range(1,5):
        for length in range(1,6):
            for w in words(q,length):
                if len(set(w)) != q:
                    continue
                for a in range(q):
                    for B in range(1,1<<q):
                        direct=any(w[i]==a and all(any(w[j]==b for j in range(i,length))
                                      for b in range(q) if B>>b&1) for i in range(length))
                        pairs=all(a==b or any(w[i]==a and w[j]==b
                                  for i in range(length) for j in range(i+1,length))
                                  for b in range(q) if B>>b&1)
                        assert direct==pairs
                        count+=1
    return count


def depth_tree(word: list[int], lo: int=0, hi: int|None=None) -> dict:
    if hi is None: hi=len(word)
    if hi-lo==1:
        return {'leaf_position':lo,'label':word[lo]}
    mid=(lo+hi)//2
    return {'ask_suffix_from_position':mid,
            'no':depth_tree(word,lo,mid),'yes':depth_tree(word,mid,hi)}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-q',type=int,default=4,choices=range(1,5))
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    args=parser.parse_args()
    if not __debug__: raise RuntimeError('Run without python -O.')
    args.output.mkdir(parents=True,exist_ok=True)
    gs,extrema,cache=graph_checks(args.max_q)
    caps=capacity_checks(cache)
    cells=positive_cell_checks()
    thresholds=[]
    for q in range(2,65):
        k=(q-1).bit_length()
        r=2*q-(1<<k)-1
        critical=threshold(q,r)
        assert 1<=r<q
        for rr in range(1,q+1):
            assert balanced_cliques(q,rr).bit_count()==threshold(q,rr)
        thresholds.append(dict(q=q,base_depth=k,jump_components=critical,r=r))
    certificates=[]
    for name, edges in [('ultrafilter_three',[(0,1),(1,2),(2,0)]),
                        ('convergent_three',arcs(3))]:
        mask=sum(1<<arcs(3).index(e) for e in edges)
        k,rem,order=min_fvs(3,mask); word=rem+order+list(reversed(rem))
        certificates.append(dict(name=name,arcs=edges,feedback_set=rem,
                                 acyclic_order=order,word=word,layers=len(word),
                                 depth=(len(word)-1).bit_length(),tree=depth_tree(word)))
    report=dict(status='all finite assertions passed',graphs=gs,
                total_graphs=sum(x['graphs'] for x in gs),
                positive_cell_word_checks=cells,
                capacity_cases=len(caps),extremal_cases=len(extrema),
                limitation='No finite computation verifies the existence of free ultrafilters or the infinite topological arguments.')
    for name,data in [('verification.json',report),('capacity_checks.json',caps),
                      ('strategy_certificates.json',certificates)]:
        (args.output/name).write_text(json.dumps(data,indent=2)+'\n')
    for name,data in [('extremal_thresholds.csv',extrema),('query_jump_thresholds.csv',thresholds)]:
        with (args.output/name).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(data[0]));writer.writeheader();writer.writerows(data)
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
