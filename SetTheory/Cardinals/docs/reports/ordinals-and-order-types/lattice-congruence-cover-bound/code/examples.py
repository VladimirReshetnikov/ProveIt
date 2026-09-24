#!/usr/bin/env python3
"""Exact worked examples and larger structured checks (standard library only)."""
from __future__ import annotations
import json
from fractions import Fraction
from pathlib import Path
from lattice_tools import (Lattice, from_edges, from_downsets, principal_labels,
    principal_congruence, all_congruences, partition_le, is_congruence)


def diamond(k: int, s: int = 1, t: int = 1) -> Lattice:
    """C_s glued M_k glued C_t; s and t count the glued endpoints."""
    if k < 2 or min(s,t) < 1:
        raise ValueError('Require k >= 2 and s,t >= 1')
    u = s-1
    atoms = list(range(s,s+k))
    v = s+k
    n = k+s+t
    edges = [(x,x+1) for x in range(u)]
    edges += [(u,a) for a in atoms] + [(a,v) for a in atoms]
    edges += [(x,x+1) for x in range(v,n-1)]
    return from_edges(n,edges)


def subdivided_diamond(k: int) -> Lattice:
    """M_k with one new element on the edge from atom 1 to the top."""
    if k < 3:
        raise ValueError('Require k >= 3')
    z, v = k+1, k+2
    return from_edges(k+3, [(0,a) for a in range(1,k+1)] +
        [(1,z),(z,v)] + [(a,v) for a in range(2,k+1)])


def boolean(d: int) -> Lattice:
    """Boolean lattice of all subsets of a d-element set."""
    if not 1 <= d <= 5:
        raise ValueError('Example constructor supports 1 <= d <= 5')
    down = tuple(sum(1 << b for b in range(1 << d) if b & a == b)
                 for a in range(1 << d))
    L = from_downsets(down)
    assert L is not None
    return L


def profile(L: Lattice, u: int) -> dict:
    labels = principal_labels(L)
    congruences = all_congruences(L,labels)
    assert all(is_congruence(L,p) for p in congruences)
    fan = L.upper[u]
    alpha = [principal_congruence(L,u,a) for a in fan]
    unique = list(dict.fromkeys(alpha))
    r,k,m = len(unique),len(fan),len(L.jr)
    ideals = sum(all(not(mask >> i & 1) or all(
        not partition_le(unique[j],unique[i]) or mask >> j & 1
        for j in range(r)) for i in range(r)) for mask in range(1 << r))
    if k >= 3:
        assert m >= r
        assert len(congruences) <= 1 << (L.n-1-k)
        assert len(congruences) <= ideals * (1 << (len(L.ji)-k))
    return dict(n=L.n, designated_vertex=u, k=k, r=r, m=m,
        ji=len(L.ji), distinct_global_labels=len(set(labels.values())),
        fan_ideal_count=ideals, congruences=len(congruences),
        density=str(Fraction(len(congruences),1 << (L.n-1))),
        profile_bound=str(Fraction(ideals,1 << (m+k))),
        skeleton_size=len(L.skeleton),
        fan_label_indices=[unique.index(a) for a in alpha],
        fan_label_order=[[i,j] for i in range(r) for j in range(r)
                         if i != j and partition_le(unique[i],unique[j])])


def serialize(L: Lattice, u: int) -> dict:
    ans=profile(L,u)
    ans.update(covers=[[x,y] for x in range(L.n) for y in L.upper[x]],
        meet_table=L.meet,join_table=L.join,
        principal_ji_labels=principal_labels(L),
        congruence_partitions=sorted(all_congruences(L)))
    return ans


def main() -> None:
    examples = {}
    examples['M2'] = serialize(diamond(2),0)
    examples['M3'] = serialize(diamond(3),0)
    examples['M4'] = serialize(diamond(4),0)
    R6 = from_edges(6,[(0,1),(0,2),(0,3),(2,4),(3,4),(1,5),(4,5)])
    examples['two_label_six_element'] = serialize(R6,0)
    S7 = from_edges(7,[(0,1),(0,2),(0,3),(1,4),(3,4),(2,5),(3,5),(4,6),(5,6)])
    examples['three_label_seven_element'] = serialize(S7,0)
    subdivided = from_edges(6,[(0,1),(0,2),(0,3),(1,4),(4,5),(2,5),(3,5)])
    examples['subdivided_M3'] = serialize(subdivided,0)
    examples['Boolean3'] = serialize(boolean(3),0)
    examples['chain_M3_chain'] = serialize(diamond(3,2,2),1)
    assert examples['two_label_six_element']['congruences'] == 3
    assert examples['three_label_seven_element']['congruences'] == 5
    structured = []
    for k in range(3,21):
        L=diamond(k)
        rec=profile(L,0)
        assert rec['congruences']==2
        structured.append(dict(family='M_k',parameter=k,**rec))
    for k,s,t in [(3,3,4),(4,2,3),(7,2,2),(10,1,3)]:
        L=diamond(k,s,t)
        rec=profile(L,s-1)
        assert rec['congruences']==1 << (s+t-1)
        structured.append(dict(family='C_s_glued_M_k_glued_C_t',s=s,t=t,**rec))
    for k in range(3,13):
        rec=profile(subdivided_diamond(k),0)
        assert rec['congruences']==3
        assert Fraction(rec['density'])==Fraction(3,1 << (k+2))
        structured.append(dict(family='subdivided_M_k',parameter=k,**rec))
    for d in (3,4,5):
        rec=profile(boolean(d),0)
        assert rec['congruences']==1 << d
        structured.append(dict(family='Boolean',dimension=d,**rec))
    root=Path(__file__).resolve().parents[1]
    (root/'data'/'examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    (root/'data'/'structured_checks.json').write_text(json.dumps(
        dict(status='PASS',cases=len(structured),records=structured),indent=2)+'\n')
    print(json.dumps({name:{key:rec[key] for key in
        ('n','k','r','m','fan_ideal_count','congruences','density','profile_bound')}
        for name,rec in examples.items()},indent=2))
    print(f'Structured cases: {len(structured)}, PASS')

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O: verification requires assertions.')
    main()
