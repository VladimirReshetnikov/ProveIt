#!/usr/bin/env python3
"""Exact finite checks for Sharp Incidence Stability.

Run with Python 3.10 or later; only the standard library is required.
These checks are supplementary certificates, not a formal proof of the theorems.
All rank, density, and exponent calculations use exact arithmetic.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import random

FACES = [
    (0,1,3),(0,1,9),(0,2,3),(0,2,9),(1,3,10),(1,7,10),
    (1,7,12),(1,9,12),(2,3,4),(2,4,9),(3,4,11),(3,10,11),
    (4,8,9),(4,8,11),(5,6,7),(5,6,11),(5,7,10),(5,10,11),
    (6,7,12),(6,8,11),(6,8,12),(8,9,12)]
EDGES = sorted({tuple(sorted(e)) for f in FACES for e in combinations(f, 2)})
ROTATION = {
    0:[1,9,2,3], 1:[0,3,10,7,12,9], 2:[3,0,9,4],
    3:[1,0,2,4,11,10], 4:[2,9,8,11,3], 5:[7,10,11,6],
    6:[11,8,12,7,5], 7:[12,1,10,5,6], 8:[9,12,6,11,4],
    9:[4,2,0,1,12,8], 10:[5,7,1,3,11],
    11:[10,3,4,8,6,5], 12:[8,9,1,7,6]}


def rref(rows: list[tuple[int, ...]] | list[list[int]], p: int,
         width: int | None = None) -> tuple[tuple[int, ...], ...]:
    """Canonical row-space basis over a prime field."""
    if not rows:
        return ()
    n = len(rows[0]) if width is None else width
    if any(len(row) != n for row in rows):
        raise ValueError('Inconsistent row widths')
    a = [[int(x) % p for x in row] for row in rows]
    pivot_row = 0
    for col in range(n):
        pivot = next((i for i in range(pivot_row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inv = pow(a[pivot_row][col], -1, p)
        a[pivot_row] = [x * inv % p for x in a[pivot_row]]
        for i in range(len(a)):
            if i != pivot_row and a[i][col]:
                c = a[i][col]
                a[i] = [(x - c*y) % p for x, y in zip(a[i], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return tuple(tuple(row) for row in a[:pivot_row])


def rank(rows, p):
    return len(rref(rows, p))


def hypergraph_density(edges):
    """Exact maximum over edge subsets, for small test hypergraphs."""
    a = len(edges[0])
    best = Fraction(0)
    maximizers = []
    for mask in range(1, 1 << len(edges)):
        es = [edges[i] for i in range(len(edges)) if mask >> i & 1]
        if len(es) < 2:
            continue
        rho = Fraction(len(es)-1, len(set().union(*map(set, es)))-a)
        if rho > best:
            best, maximizers = rho, [mask]
        elif rho == best:
            maximizers.append(mask)
    return best, maximizers


def submodular(f):
    n = len(f).bit_length()-1
    full = (1 << n)-1
    if f[0] != 0:
        return False
    for a in range(full+1):
        for i in range(n):
            if a >> i & 1:
                continue
            if f[a] > f[a | (1 << i)]:
                return False
            for j in range(i+1, n):
                if a >> j & 1:
                    continue
                if (f[a | (1 << i)] + f[a | (1 << j)] <
                        f[a] + f[a | (1 << i) | (1 << j)]):
                    return False
    return True


def contraction(f, e):
    bit = 1 << e
    if f[bit] <= 0:
        raise ValueError('The chosen singleton must have positive rank')
    return [min(f[s], f[s | bit]-1) for s in range(len(f))]


def fractional_constant(rows, weights, n):
    """Sharp constant, as a Fraction, for a separating fractional cover."""
    result = Fraction(0)
    for f in range(1, 1 << n):
        if f.bit_count() < 2:
            continue
        c = sum((w for s, w in zip(rows, weights) if s & f), Fraction())-1
        if c <= 0:
            raise ValueError('The cover has no finite stability constant')
        result = max(result, Fraction(f.bit_count()-1)/c)
    return result


def check_complex():
    assert len(EDGES) == 33
    triangles = {tri for tri in combinations(range(13), 3)
                 if all(e in EDGES for e in combinations(tri, 2))}
    assert triangles == set(FACES)
    pair_counts = Counter(e for f in FACES for e in combinations(f, 2))
    assert set(pair_counts.values()) == {2}
    assert [sum(i in e for e in EDGES) for i in range(13)] == [4,6,4,6,5,4,5,5,5,6,5,6,5]
    darts = {(x,y) for x,y in EDGES} | {(y,x) for x,y in EDGES}
    assert all(set(ROTATION[v]) == {u for x,u in darts if x == v} for v in ROTATION)
    unseen = set(darts)
    boundary_cycles = []
    while unseen:
        start = min(unseen)
        current = start
        face = []
        while True:
            assert current in unseen
            unseen.remove(current)
            u,v = current
            face.append(u)
            cyc = ROTATION[v]
            current = (v, cyc[(cyc.index(u)+1) % len(cyc)])
            if current == start:
                break
        boundary_cycles.append(face)
    assert len(boundary_cycles) == 22
    assert all(len(f) == 3 for f in boundary_cycles)
    assert {tuple(sorted(f)) for f in boundary_cycles} == set(FACES)
    assert 13-33+len(boundary_cycles) == 2
    seen = {0}
    while True:
        enlarged = seen | {y for x,y in darts if x in seen}
        if enlarged == seen:
            break
        seen = enlarged
    assert len(seen) == 13
    maxrho = Fraction(0)
    maximizers = []
    vertex_sets_checked = 0
    for mask in range(1 << 13):
        n = mask.bit_count()
        if n < 3:
            continue
        m = sum(bool(mask >> u & 1 and mask >> v & 1) for u,v in EDGES)
        assert m <= 3*n-6
        vertex_sets_checked += 1
        if m < 2:
            continue
        rho = Fraction(m-1, n-2)
        if rho > maxrho:
            maxrho, maximizers = rho, [mask]
        elif rho == maxrho:
            maximizers.append(mask)
    assert maxrho == Fraction(32,11) and maximizers == [(1 << 13)-1]
    return {'vertices':13, 'edges':33, 'faces':22, 'triangles':22,
            'rotation_system_euler_characteristic':2,
            'vertex_subsets_checked':vertex_sets_checked,
            'm2':str(maxrho), 'unique_maximizer':'all 33 edges'}


def check_subspaces(rng):
    examples = [list(combinations(range(3),2)), list(combinations(range(4),2)),
                [(0,1),(1,2),(2,3),(0,3)],
                [(0,1,2),(0,1,3),(0,2,3),(1,2,3)],
                [(0,1),(2,3),(4,5)]]
    total = 0
    for edges in examples:
        mu,_ = hypergraph_density(edges)
        a = len(edges[0])
        vertices = sorted(set().union(*map(set, edges)))
        for p in (2,3,5):
            for _ in range(80):
                spaces = []
                for e in edges:
                    rows = [tuple(rng.randrange(p) for _ in range(6))
                            for _ in range(rng.randrange(4))]
                    spaces.append(list(rref(rows,p)))
                t = sum(len(h) for h in spaces)
                k = rank([x for h in spaces for x in h],p)
                kv = [rank([x for e,h in zip(edges,spaces) if v in e for x in h],p)
                      for v in vertices]
                R, delta = t-k, sum(kv)-a*k
                assert R <= mu*delta
                # Greedy union-basis certificate for optimal directness repair.
                chosen = []
                selected_per_edge = [[] for _ in edges]
                for i,h in enumerate(spaces):
                    for x in h:
                        if rank(chosen+[x],p) > len(chosen):
                            chosen.append(x)
                            selected_per_edge[i].append(x)
                assert len(chosen) == k
                assert sum(len(x) for x in selected_per_edge) == k
                assert t-sum(len(x) for x in selected_per_edge) == R
                total += 1
        # Exact equality witness on every density-maximizing edge support.
        for mask in hypergraph_density(edges)[1]:
            F = [edges[i] for i in range(len(edges)) if mask >> i & 1]
            assert Fraction(len(F)-1, len(set().union(*map(set,F)))-a) == mu
    return {'random_arrangements':total, 'prime_fields':[2,3,5],
            'directness_repair_certificates':total}


def check_polymatroids(rng):
    n = 5
    covers = [([((1<<n)-1) ^ (1<<i) for i in range(n)], [Fraction(1,n-1)]*n),
              ([(1<<i)|(1<<((i+1)%n)) for i in range(n)], [Fraction(1,2)]*n),
              ([1<<i for i in range(n)] + [(1<<n)-1], [Fraction(1,2)]*(n+1)),
              ([(1<<n)-1], [Fraction(2)])]
    checked = contractions = 0
    for _ in range(80):
        # Sum of a representable rank and a coverage polymatroid.
        blocks = [[tuple(rng.randrange(2) for _ in range(5))
                   for _ in range(rng.randrange(1,3))] for i in range(n)]
        atoms = [rng.randrange(1,1<<n) for _ in range(4)]
        f = [rank([x for i in range(n) if s>>i&1 for x in blocks[i]],2)
             + sum(bool(s & atom) for atom in atoms) for s in range(1<<n)]
        assert submodular(f)
        for rows,weights in covers:
            K = fractional_constant(rows,weights,n)
            R = sum(f[1<<i] for i in range(n))-f[-1]
            gap = sum(w*f[s] for s,w in zip(rows,weights))-f[-1]
            assert R <= K*gap
            for F in range(1,1<<n):
                if F.bit_count()<2:
                    continue
                ff = [int(bool(s&F)) for s in range(1<<n)]
                RR = sum(ff[1<<i] for i in range(n))-ff[-1]
                GG = sum(w*ff[s] for s,w in zip(rows,weights))-ff[-1]
                assert RR <= K*GG
            checked += 1
        while f[-1] > 0:
            e = next(i for i in range(n) if f[1<<i]>0)
            fp = contraction(f,e)
            assert submodular(fp) and fp[-1] == f[-1]-1
            for rows,weights in covers:
                K = fractional_constant(rows,weights,n)
                Rdiff = sum(f[1<<i]-fp[1<<i] for i in range(n))-1
                Gdiff = sum(w*(f[s]-fp[s]) for s,w in zip(rows,weights))-1
                assert Rdiff <= K*Gdiff
            f = fp
            contractions += 1
    return {'polymatroid_cover_checks':checked, 'unit_contractions':contractions}


def check_equality():
    """Exhaust all assignments of F_2^2 subspaces to K_3 and K_4 edges."""
    candidates=[(),((1,0),),((0,1),),((1,1),),((1,0),(0,1))]
    vectors=list(product(range(2),repeat=2))
    point_sets=[]
    for h in candidates:
        point_sets.append({x for x in vectors if rank(list(h)+[x],2)==len(h)})
    total=equalities=0
    for n in (3,4):
        edges=list(combinations(range(n),2))
        mu=Fraction(n+1,2)
        for assignment in product(range(5),repeat=len(edges)):
            spaces=[candidates[i] for i in assignment]
            t=sum(len(h) for h in spaces)
            k=rank([x for h in spaces for x in h],2)
            ki=[rank([x for e,h in zip(edges,spaces) if v in e for x in h],2)
                for v in range(n)]
            common=set(vectors)
            for i in assignment:
                common &= point_sets[i]
            c=(len(common)).bit_length()-1
            R=t-k
            delta=sum(ki)-2*k
            eq=(R==mu*delta)
            structure=(R==(len(edges)-1)*c)
            assert eq==structure
            equalities+=eq
            total+=1
    return {'exhaustive_arrangements':total,'equality_cases':equalities,
            'ambient_space':'F_2^2','graphs':['K3','K4']}


def check_exterior(rng):
    edges = list(combinations(range(4),2))
    checked = 0
    for p in (2,3,5):
        for _ in range(60):
            h = [rng.randrange(3) for _ in edges]
            t = sum(h)
            if not t:
                continue
            rows = [tuple(rng.randrange(p) for _ in range(5)) for _ in range(t)]
            # Edge-block injectivity is required by the counting statement.
            blocks=[]; start=0
            for d in h:
                blocks.append(list(range(start,start+d))); start+=d
            if any(rank([rows[i] for i in b],p) != len(b) for b in blocks):
                continue
            k = rank(rows,p); R=t-k
            star_indices = [[i for e,b in zip(edges,blocks) if v in e for i in b]
                            for v in range(4)]
            ti = [len(s) for s in star_indices]
            ki = [rank([rows[i] for i in s],p) for s in star_indices]
            coordinate_pairs = set(pair for s in star_indices for pair in combinations(s,2))
            l0 = len(coordinate_pairs)
            assert l0 == sum(x*(x-1)//2 for x in ti)-sum(x*(x-1)//2 for x in h)
            wedge_rows=[]
            for i,j in coordinate_pairs:
                x,y=rows[i],rows[j]
                wedge_rows.append(tuple((x[a]*y[b]-x[b]*y[a])%p for a,b in combinations(range(5),2)))
            ell=rank(wedge_rows,p)
            b=l0-ell
            assert 0 <= b <= R*k+R*(R-1)//2
            A=sum(x*(x-1)//2-y*(y-1)//2 for x,y in zip(ti,ki))
            old = R*k-sum(x*x for x in h)-ell+sum(x*(x-1)//2 for x in ki)
            new = -sum(x*(x+1)//2 for x in h)+R*k+b-A
            assert old == new
            checked += 1
    return {'exterior_rank_and_cancellation_checks':checked}


def omega(x,y,p):
    D=len(x)//2
    return sum(x[i]*y[D+i]-x[D+i]*y[i] for i in range(D))%p


def check_symplectic():
    report={}
    for p in (2,3):
        vectors=[x for x in product(range(p),repeat=4) if any(x)]
        spaces=set()
        grams=Counter()
        for x in vectors:
            for y in vectors:
                rr=rref([x,y],p)
                if len(rr)!=2:
                    continue
                grams[omega(x,y,p)]+=1
                if omega(x,y,p)==0:
                    spaces.add(rr)
        assert len(spaces)==(p+1)*(p*p+1)
        assert all(value<=p**7 for value in grams.values())
        lines={rref([x],p) for x in vectors}
        for line in lines:
            contained=sum(rank(list(L)+list(line),p)==2 for L in spaces)
            assert Fraction(contained,len(spaces))==Fraction(1,p*p+1)
        report[str(p)]={'lagrangians':len(spaces), 'lines':len(lines),
                        'ordered_independent_pair_gram_counts':dict(grams)}
    return report


def check_exponents():
    B=lambda r:(263*r-3*r*r)//2-33
    j=lambda r:(11*r+31)//32
    rows=[]
    for s in range(1,23):
        candidates=[r for r in range(1,65) if j(r)==s]
        best=max(B(r) for r in candidates)
        rows.append({'j':s,'R_min':min(candidates),'R_max':max(candidates),
                     'B_max':best,'at_310':best-310*s,'at_364':best-364*s})
    assert max(row['at_310'] for row in rows)==-7
    assert max(row['at_364'] for row in rows)==-140
    for m in range(1,34):
        for R in range(1,2*m-1):
            bound=-m+4*m*R-(3*R*R+R)//2
            assert bound <= B(R)
    return {'grouped_bounds':rows,
            'max_exponent_D310':-7, 'max_exponent_D364':-140,
            'uniform_bound_for_D_ge_364':'-D + 224'}


def main():
    rng=random.Random(20261007)
    report={'seed':20261007,'arithmetic':'exact integer / rational / prime-field',
            'complex':check_complex(),
            'subspaces':check_subspaces(rng),
            'polymatroids':check_polymatroids(rng),
            'equality_classification':check_equality(),
            'exterior_algebra':check_exterior(rng),
            'symplectic_counts':check_symplectic(),
            'exponents':check_exponents(),
            'status':'ALL CHECKS PASSED',
            'limitations':'Finite checks supplement the written proofs; no Lean compilation is claimed.'}
    destination=Path(__file__).resolve().parents[1]/'certificates'/'verification_results.json'
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
