"""Independent finite verification of the two-flow bijections.

Run from any directory: python code/verify.py --suite all
The checks enumerate graphs, demand inequalities and matching permutations;
they are finite evidence, not a replacement for the article's proofs.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import asdict, replace
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from pathlib import Path
from random import Random
from time import perf_counter

from transport_bijection import BipartiteDemand, preorder_graph

OUT = Path(__file__).resolve().parent.parent / 'data'


def subsets(n, size=None):
    for k in range(n+1) if size is None else [size]:
        yield from combinations(range(n), k)


def bounded_vectors(n, m):
    if n == 0:
        yield ()
    else:
        for first in range(m+1):
            for tail in bounded_vectors(n-1, m-first):
                yield (first,) + tail


def brute_match(H, I, J):
    return len(I) == len(J) and any(all((x, y) in H.edges for x, y in zip(I, p))
                                   for p in permutations(J))


def hall(H, c):
    for A in subsets(H.n):
        neighbors = {x for x, y in H.edges if y in A}
        if sum(c[y] for y in A) > len(neighbors):
            return False
    return True


def check_graph(H):
    """All pairs and all vectors, independently tested on both sides."""
    image, pairs = {}, 0
    for k in range(min(H.m, H.n)+1):
        for I in subsets(H.m, k):
            for J in subsets(H.n, k):
                feasible = brute_match(H, I, J)
                assert H.matchable(I, J) == feasible
                if not feasible:
                    continue
                c, forward = H.basis_to_demand(I, J, certificate=True)
                assert hall(H, c), (H.edges, I, J, c)
                fast, core = H.basis_to_demand_core(I,J,certificate=True)
                assert fast == c
                if J: H.verify_core_certificate(c,core)
                assert tuple(y for y, v in enumerate(c) if v) == J
                assert c not in image, (H.edges, I, J, c, image.get(c))
                pair, inverse = H.demand_to_basis(c, certificate=True)
                assert pair == (I, J), (H.edges, I, J, c, pair)
                if J:
                    assert {(x,y) for x,y,_ in forward.flow} == {(x,y) for x,y,_ in inverse.flow}
                    H.verify_certificate(forward)
                    H.verify_certificate(inverse)
                image[c] = (I, J)
                pairs += 1
    demands = {c for c in bounded_vectors(H.n, H.m) if hall(H, c)}
    assert set(image) == demands, (H.edges, set(image) ^ demands)
    for c in demands:
        assert H.is_demand(c)
    return pairs


def exhaustive(max_m, max_n, min_m=0, min_n=0):
    graphs = pairs = 0
    by_size = []
    for m in range(min_m, max_m+1):
        for n in range(min_n, max_n+1):
            gp = pp = 0
            edges = list(product(range(m), range(n)))
            for mask in range(1 << len(edges)):
                H = BipartiteDemand(m, n, (e for i,e in enumerate(edges) if (mask>>i)&1))
                pp += check_graph(H); gp += 1
            graphs += gp; pairs += pp
            by_size.append({'m':m,'n':n,'graphs':gp,'support_pairs':pp})
    return {'graphs':graphs, 'support_pairs':pairs, 'by_size':by_size}


def preorders(max_n=4):
    count = vectors = 0
    by_size = []
    for n in range(max_n+1):
        edges = [(i,j) for i in range(n) for j in range(n) if i != j]
        pn = vn = 0
        for mask in range(1 << len(edges)):
            rows = [{i} for i in range(n)]
            for k,(i,j) in enumerate(edges):
                if (mask>>k)&1: rows[i].add(j)
            if any(not rows[j] <= rows[i] for i in range(n) for j in rows[i]):
                continue
            H = preorder_graph(rows)
            ideals = [set(A) for A in subsets(n)
                      if all(not (j in A and i not in A) for i in range(n) for j in rows[i])]
            demands = []
            for c in bounded_vectors(n,n):
                in_polytope = all(sum(c[i] for i in A) <= len(A) for A in ideals)
                assert in_polytope == hall(H,c)
                if in_polytope:
                    I,J = H.demand_to_basis(c)
                    assert H.basis_to_demand(I,J) == c
                    demands.append(c)
            pn += 1; vn += len(demands)
        by_size.append({'n':n,'preorders':pn,'lattice_points':vn})
        count += pn; vectors += vn
    return {'preorders':count,'lattice_points':vectors,'by_size':by_size}


def compatible(H, I, J, c):
    """Receiver restriction and every single unused-supplier deletion."""
    checks = 0
    G = BipartiteDemand(H.m,H.n, ((x,y) for x,y in H.edges if y in J))
    G.cost = {e:w for e,w in H.cost.items() if e[1] == -1 or e[1] in J}
    assert G.basis_to_demand(I,J) == c
    checks += 1
    if not J:
        return checks
    _,cert = H.basis_to_demand(I,J,certificate=True)
    leaf = {x:y for x,y,_ in cert.flow if x not in I}
    for x in range(H.m):
        if x in I: continue
        new_x = {old: old-int(old>x) for old in range(H.m) if old != x}
        G = BipartiteDemand(H.m-1,H.n, ((new_x[a],b) for a,b in H.edges if a != x))
        G.cost = {(new_x[a],b):w for (a,b),w in H.cost.items() if a != x}
        cc = list(c)
        if leaf[x] != -1: cc[leaf[x]] -= 1
        assert G.basis_to_demand(tuple(new_x[a] for a in I),J) == tuple(cc)
        checks += 1
    return checks


def random_checks(seed=20260930, cases=250):
    rng=Random(seed)
    pair_count = compat = gauges = 0
    for case in range(cases):
        m, n = rng.randrange(1,8), rng.randrange(1,7)
        edges = [(x,y) for x in range(m) for y in range(n) if rng.random()<rng.uniform(.2,.9)]
        order = edges + [(x,-1) for x in range(m)]
        rng.shuffle(order)
        H = BipartiteDemand(m,n,edges,order)
        for _ in range(24):
            k=rng.randrange(min(m,n)+1)
            I=tuple(sorted(rng.sample(range(m),k))); J=tuple(sorted(rng.sample(range(n),k)))
            if not brute_match(H,I,J): continue
            c=H.basis_to_demand(I,J)
            assert H.demand_to_basis(c)==(I,J)
            assert H.basis_to_demand_core(I,J)==c
            assert hall(H,c)
            compat += compatible(H,I,J,c)
            # Same cycle-sign chamber: replace binary powers by ternary ones.
            G=BipartiteDemand(m,n,edges,order)
            G.cost={e:3**i for i,e in enumerate(order)}
            assert G.basis_to_demand(I,J)==c
            # Nonnegative row/column gauge, including dummy column.
            a=[rng.randrange(50) for _ in range(m)]
            b={y:rng.randrange(50) for y in (-1,*range(n))}
            G.cost={e:w+a[e[0]]+b[e[1]] for e,w in H.cost.items()}
            assert G.basis_to_demand(I,J)==c
            gauges += 2; pair_count += 1
    return {'seed':seed,'graphs':cases,'support_pairs':pair_count,
            'restriction_deletion_checks':compat,'chamber_gauge_checks':gauges}


def exact_chain():
    H=BipartiteDemand(3,3,[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2)])
    bases=[frozenset(B) for B in combinations(range(6),3) if H.is_lifted_basis(B)]
    index={B:i for i,B in enumerate(bases)}
    records=[]
    for weights in ([1]*6,[1,1,1,2,3,5]):
        def wt(B):
            result=1
            for e in B: result*=weights[e]
            return result
        Z=sum(wt(B) for B in bases)
        pi=[Fraction(wt(B),Z) for B in bases]
        P=[[Fraction(0) for _ in bases] for _ in bases]
        for i,B in enumerate(bases):
            for removed in B:
                A=B-{removed}
                options=[e for e in range(6) if e not in A and A|{e} in index]
                denom=sum(weights[e] for e in options)
                for e in options:
                    P[i][index[A|{e}]]+=Fraction(weights[e],3*denom)
        assert all(sum(row)==1 for row in P)
        assert all(pi[i]*P[i][j]==pi[j]*P[j][i] for i in range(len(bases)) for j in range(len(bases)))
        points=[H.decode_lifted_basis(B) for B in bases]
        assert len(set(points))==len(bases)
        for i,c in enumerate(points):
            expected=1
            for y,v in enumerate(c):
                if v: expected*=weights[3+y]
            assert pi[i]==Fraction(expected,Z)
        # Exact finite-time distance before/after the bijection.
        law=[Fraction(int(B==frozenset(range(3)))) for B in bases]
        for _ in range(8):
            law=[sum(law[i]*P[i][j] for i in range(len(bases))) for j in range(len(bases))]
        tv=sum(abs(law[i]-pi[i]) for i in range(len(bases)))/2
        records.append({'weights':weights,'partition_function':Z,'states':len(bases),
                        'tv_after_8_steps':str(tv),'tv_decimal':float(tv)})
    # Tamper with both primal and dual certificates; each must be rejected.
    c,cert=H.basis_to_demand((0,1),(0,1),certificate=True)
    bads=[replace(cert,row_margins=(cert.row_margins[0]+1,)+cert.row_margins[1:]),
          replace(cert,row_potentials=(cert.row_potentials[0]+1,)+cert.row_potentials[1:]),
          replace(cert,flow=cert.flow[:-1])]
    for bad in bads:
        try: H.verify_certificate(bad)
        except ValueError: pass
        else: raise AssertionError('tampered certificate accepted')
    return {'chains':records,'tampered_certificates_rejected':len(bads)}


def example():
    H=BipartiteDemand(4,3,[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2)])
    I,J=(0,1,3),(0,1,2)
    c,A=H.basis_to_demand(I,J,certificate=True)
    pair,B=H.demand_to_basis(c,certificate=True)
    return {'suppliers':I,'receivers':J,'demand':c,
            'costs':[[x,y,w] for (x,y),w in H.cost.items()],
            'forward_certificate':asdict(A),'inverse_certificate':asdict(B),
            'core_certificate':asdict(H.basis_to_demand_core(I,J,certificate=True)[1])}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--suite',choices=['small','four_by_three','preorders','random','chain','example','all'],default='all')
    args=parser.parse_args()
    suites={'small':lambda:exhaustive(3,3),
            'four_by_three':lambda:exhaustive(4,3,4,3),
            'preorders':preorders,'random':random_checks,
            'chain':exact_chain,'example':example}
    OUT.mkdir(parents=True,exist_ok=True)
    for name,fn in suites.items():
        if args.suite not in (name,'all'): continue
        started=perf_counter()
        result=fn()
        report={'suite':name,'passed':True,'elapsed_seconds':round(perf_counter()-started,3),**result}
        (OUT/f'{name}.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report),flush=True)

if __name__=='__main__': main()
