#!/usr/bin/env python3
"""Exact finite checks for Matroid Lifts of Matching Supports and Preorder Polynomials.
Python >= 3.10; standard library only. No numerical roots, random tests or CAS.
Run: python3 verify.py --output verification_results.json
These finite checks supplement, and do not replace, the proofs in article.tex.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from collections import Counter
from fractions import Fraction
from itertools import product, permutations
from pathlib import Path


def require(test: bool, message: str) -> None:
    if not test:
        raise AssertionError(message)


def bits(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def matchable_pairs(rows: tuple[int, ...], r: int) -> list[tuple[int, int]]:
    """Enumerate supports, once each, by a set-valued matching dynamic program."""
    dp: list[set[int]] = [{0}]
    for I in range(1, 1 << len(rows)):
        b = I & -I
        i = b.bit_length() - 1
        targets: set[int] = set()
        for J in dp[I ^ b]:
            for j in bits(rows[i] & ~J):
                targets.add(J | (1 << j))
        dp.append(targets)
    return [(I, J) for I, targets in enumerate(dp) for J in sorted(targets)]


def base_masks(rows: tuple[int, ...], r: int) -> set[int]:
    full = (1 << r) - 1
    return {I | ((full ^ J) << len(rows)) for I, J in matchable_pairs(rows, r)}


def subset_products(weights: tuple[int | Fraction, ...]) -> list[int | Fraction]:
    out: list[int | Fraction] = [1]
    for mask in range(1, 1 << len(weights)):
        b = mask & -mask
        out.append(out[mask ^ b] * weights[b.bit_length() - 1])
    return out


def coeffs(rows, r, left=None, right=None):
    l = len(rows)
    a = [0] * (min(l, r) + 1)
    L = subset_products(tuple(left) if left is not None else (1,) * l)
    R = subset_products(tuple(right) if right is not None else (1,) * r)
    for I, J in matchable_pairs(rows, r):
        a[I.bit_count()] += L[I] * R[J]
    return a


def check_ulc(a, d):
    require(len(a) == d + 1, 'Incorrect ULC order')
    for k in range(1, d):
        require(a[k] ** 2 * k * (d-k) >=
                a[k-1] * a[k+1] * (k+1) * (d-k+1),
                f'ULC failure: {a}, order {d}, index {k}')
    nz = [k for k, x in enumerate(a) if x]
    require(not nz or nz == list(range(min(nz), max(nz)+1)), 'Internal zero')


def is_transitive(rows):
    return all((rows[j] & ~rows[i]) == 0
               for i in range(len(rows)) for j in bits(rows[i]))


def swap_pair(mask, i, n):
    if ((mask >> i) & 1) != ((mask >> (n+i)) & 1):
        return mask ^ (1 << i) ^ (1 << (n+i))
    return mask


def all_clones(bases, n):
    return all(swap_pair(C, i, n) in bases for C in bases for i in range(n))


def upsets(rows):
    return [U for U in range(1 << len(rows))
            if all(rows[i] & ~U == 0 for i in bits(U))]


def compositions(total, length):
    if length == 0:
        if total == 0:
            yield ()
        return
    for x in range(total + 1):
        for tail in compositions(total-x, length-1):
            yield (x,) + tail


def lattice_h(rows):
    n = len(rows)
    full = (1 << n) - 1
    ideals = [full ^ U for U in upsets(rows)]
    ans = [0] * (n+1)
    for total in range(n+1):
        for c in compositions(total, n):
            if all(sum(c[i] for i in bits(D)) <= D.bit_count() for D in ideals):
                ans[sum(x > 0 for x in c)] += 1
    return ans


def gamma_expansion(rows, weights=None):
    n = len(rows)
    w = subset_products(tuple(weights) if weights else (1,) * n)
    gamma = [Fraction(0)] * (n//2 + 1)
    for I, J in matchable_pairs(rows, n):
        if not I & J:
            gamma[I.bit_count()] += Fraction(w[I], w[J])
    expanded = [Fraction(0)] * (n+1)
    for k, g in enumerate(gamma):
        for q in range(n-2*k+1):
            expanded[k+q] += g * math.comb(n-2*k, q)
    return gamma, expanded


def match_rank(neighbors, slots):
    """Independent augmenting-path maximum matching, separate from support DP."""
    owner = [-1] * slots
    def augment(i, seen):
        for j in bits(neighbors[i]):
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = i
                return True
        return False
    return sum(augment(i, set()) for i in range(len(neighbors)))


def test_bipartite():
    count = 0
    for l, r in [(1,1),(2,2),(2,3),(3,3),(3,4)]:
        for emask in range(1 << (l*r)):
            rows = tuple((emask >> (i*r)) & ((1 << r)-1) for i in range(l))
            a = coeffs(rows, r)
            check_ulc(a, min(l,r))
            check_ulc(coeffs(rows, r, (2,3,5)[:l], (7,11,13,17)[:r]), min(l,r))
            bases = base_masks(rows, r)
            require(len(bases) == sum(a), 'Support/base bijection')
            # Verify the claimed matroid by an independent slot-matching oracle.
            for C in range(1 << (l+r)):
                if C.bit_count() != r:
                    continue
                ns = [rows[i] if i < l else 1 << (i-l) for i in bits(C)]
                require((C in bases) == (match_rank(ns, r) == r), 'Base oracle')
            count += 1
    return count


def transposition(mask, i, j):
    if ((mask >> i) & 1) != ((mask >> j) & 1):
        return mask ^ (1 << i) ^ (1 << j)
    return mask


def permute_mask(mask, perm):
    return sum(1 << perm[i] for i in bits(mask))


def check_structure(rows, bases):
    n = len(rows)
    # Verify the entire intrinsic clone equivalence relation.
    for i in range(2*n):
        for j in range(i+1,2*n):
            clones = all(transposition(C,i,j) in bases for C in bases)
            equivalent = bool(rows[i % n] >> (j % n) & 1 and
                              rows[j % n] >> (i % n) & 1)
            require(clones == equivalent, 'Intrinsic clone classes')
    transposed = tuple(sum(1 << i for i in range(n) if rows[i] >> j & 1)
                       for j in range(n))
    require({((1 << (2*n))-1) ^ C for C in bases} == base_masks(transposed,n),
            'Matroid dual/order dual identity')
    if n <= 3:
        actual = sum(all(permute_mask(C,p) in bases for C in bases)
                     for p in permutations(range(2*n)))
        order_aut = sum(all(bool(rows[i] >> j & 1) == bool(rows[p[i]] >> p[j] & 1)
                            for i in range(n) for j in range(n))
                        for p in permutations(range(n)))
        unseen = set(range(n)); sizes=[]
        while unseen:
            i=min(unseen)
            block={j for j in unseen if rows[i] >> j & 1 and rows[j] >> i & 1}
            sizes.append(len(block));unseen-=block
        expected = order_aut * math.prod(math.factorial(2*m) for m in sizes)
        expected //= math.prod(math.factorial(m) for m in sizes)
        require(actual == expected, 'Full automorphism-group order')
    return n <= 3


def test_relations():
    counts, rank_checks, automorphism_checks = {}, 0, 0
    for n in range(1,5):
        off = [(i,j) for i in range(n) for j in range(n) if i != j]
        rc = pc = 0
        for emask in range(1 << len(off)):
            rows = [1 << i for i in range(n)]
            for q, (i,j) in enumerate(off):
                if emask >> q & 1:
                    rows[i] |= 1 << j
            rows = tuple(rows)
            bases = base_masks(rows, n)
            trans = is_transitive(rows)
            require(all_clones(bases,n) == trans, 'Clone/transitivity equivalence')
            a = coeffs(rows,n)
            check_ulc(a,n)
            require((a == list(reversed(a))) == trans, 'Palindromicity criterion')
            rc += 1
            if not trans:
                continue
            pc += 1
            automorphism_checks += check_structure(rows,bases)
            require(lattice_h(rows) == a, 'Lattice-point/support identity')
            g, expanded = gamma_expansion(rows)
            require(expanded == a, 'Unweighted gamma expansion')
            weights = (2,3,5,7)[:n]
            wg, expanded = gamma_expansion(rows, weights)
            wa = coeffs(rows,n,weights,tuple(Fraction(1,w) for w in weights))
            require(expanded == wa, 'Weighted gamma expansion')
            require(wa == list(reversed(wa)), 'Weighted palindromicity')
            check_ulc(wa,n)
            ups = upsets(rows)
            for X in range(1 << (2*n)):
                oracle_rank = max((X & C).bit_count() for C in bases)
                formula_rank = min(U.bit_count() +
                    (X & ~ (U | U << n)).bit_count() for U in ups)
                symmetric_rank = match_rank([rows[i % n] for i in bits(X)], n)
                require(oracle_rank == formula_rank == symmetric_rank, 'Rank formula')
                rank_checks += 1
        counts[str(n)] = {'reflexive_relations': rc, 'preorders': pc}
    return counts, rank_checks, automorphism_checks


def test_minor_universality():
    count = 0
    for l,r in [(2,2),(2,3),(3,3)]:
        n = l+r
        for emask in range(1 << (l*r)):
            rows = tuple((emask >> (i*r)) & ((1 << r)-1) for i in range(l))
            prows = tuple((1 << i) | (rows[i] << l) if i < l else 1 << i
                          for i in range(n))
            nbases = base_masks(prows,n)
            contracted = ((1 << l)-1) << n
            deleted = ((1 << r)-1) << (n+l)
            minor_bases = {C & ((1 << n)-1) for C in nbases
                           if C & contracted == contracted and not C & deleted}
            require(minor_bases == base_masks(rows,r), 'Fundamental-matroid minor')
            # Restrict the minor to A; verify every independent set of T.
            for I in range(1 << l):
                independent = any(I & C == I for C in minor_bases)
                require(independent == (match_rank([rows[i] for i in bits(I)],r)
                                         == I.bit_count()), 'Transversal restriction')
            count += 1
    return count


def feasible_sets(n, edges):
    adj = [0]*n
    for u,v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    good = {0}
    for S in range(1,1 << n):
        if S.bit_count() % 2:
            continue
        b = S & -S
        i = b.bit_length()-1
        if any((S ^ b ^ (1 << j)) in good for j in bits(adj[i] & S)):
            good.add(S)
    return good


def phi_dict(n, edges):
    return {tuple(int(not (S >> i & 1)) for i in range(n)):
            (-1)**(S.bit_count()//2) for S in feasible_sets(n,edges)}


def poly_mul(a,b):
    out = Counter()
    for x,c in a.items():
        for y,d in b.items():
            out[tuple(u+v for u,v in zip(x,y))] += c*d
    return {e:c for e,c in out.items() if c}


def derivative(p,i):
    out = {}
    for e,c in p.items():
        if e[i]:
            f=list(e); f[i]-=1
            out[tuple(f)] = c*e[i]
    return out


def test_gluing_and_witness():
    graphs = [(2,[(0,1)]), (4,[(0,1),(1,2),(2,3),(3,0)]),
              (5,[(i,j) for i in (0,1) for j in (2,3,4)]),
              (6,[(i,j) for i in (0,1,2) for j in (3,4,5)])]
    tests=0
    for n1,e1 in graphs:
        for n2,e2 in graphs:
            n=n1+n2-1
            def place(p, second=False):
                out={}
                for e,c in p.items():
                    ex=[0]*n
                    for i,v in enumerate(e):
                        ex[(n1+i-1 if i else 0) if second else i]=v
                    out[tuple(ex)]=c
                return out
            f1=place(phi_dict(n1,e1)); f2=place(phi_dict(n2,e2),True)
            a1=derivative(f1,0); a2=derivative(f2,0)
            ans=Counter(poly_mul(f1,a2)); ans.update(poly_mul(a1,f2))
            for e,c in poly_mul(a1,a2).items():
                ex=list(e);ex[0]+=1
                ans[tuple(ex)]-=c
            edges=e1+[(0 if u==0 else n1+u-1,0 if v==0 else n1+v-1) for u,v in e2]
            require({e:c for e,c in ans.items() if c} == phi_dict(n,edges), 'Vertex sum')
            tests+=1
    edges=[(0,2),(2,3),(3,1),(0,4),(4,5),(5,1),(0,6),(6,7),(7,1)]
    good=feasible_sets(8,edges)
    p=[sum(S.bit_count()==2*k for S in good) for k in range(5)]
    require(p == [1,9,24,16,1], 'Theta support polynomial')
    f=phi_dict(8,edges)
    values=[0,0,3,2,-2,-2,2,2]
    def evaluate(pol):
        return sum(c * math.prod(v**e for v,e in zip(values,exp))
                   for exp,c in pol.items())
    ray=evaluate(derivative(f,0))*evaluate(derivative(f,1))-evaluate(f)*evaluate(derivative(derivative(f,0),1))
    require(ray == -9, 'Theta Rayleigh witness')
    # h=(1+t)^8 p(t/(1+t)^2).
    h=[sum(p[k]*math.comb(8-2*k,j-k) for k in range(5)
           if 0 <= j-k <= 8-2*k) for j in range(9)]
    check_ulc(h,8)
    # Certify the positively rescaled Sturm chain printed in the article.
    chain = [[1,9,24,16,1], [9,48,48,4], [32,165,144], [1120,4557], [-1]]
    def remainder(a,b):
        a=list(map(Fraction,a)); b=list(map(Fraction,b))
        while len(a) >= len(b) and any(a):
            q=a[-1]/b[-1]; shift=len(a)-len(b)
            for j,c in enumerate(b):
                a[shift+j]-=q*c
            while a and a[-1]==0:
                a.pop()
        return a
    for j in range(3):
        rem=[-x for x in remainder(chain[j],chain[j+1])]
        target=chain[j+2]
        require(len(rem)==len(target), 'Sturm degree')
        ratio=rem[-1]/target[-1]
        require(ratio>0 and all(x==ratio*y for x,y in zip(rem,target)),
                'Sturm negative-remainder sign certificate')
    def variations(signs):
        return sum(x!=y for x,y in zip(signs,signs[1:]))
    plus=[1 if q[-1]>0 else -1 for q in chain]
    minus=[sgn*(-1)**(len(q)-1) for sgn,q in zip(plus,chain)]
    roots=variations(minus)-variations(plus)
    require(roots==2,'Theta real-root count')
    return tests, {'theta_p':p,'theta_h':h,'rayleigh_value':ray,
                   'rayleigh_variables':[2,3,4,5,6,7],
                   'rayleigh_assignment':values[2:],
                   'sturm_chain_valid':True,'real_roots_of_theta_p':roots}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=parser.parse_args()
    start=time.perf_counter()
    result={'status':'PASS','arithmetic':'integers and exact rational numbers',
            'scope':'finite checks only; not a formal proof'}
    result['bipartite_graphs']=test_bipartite()
    (result['relations_by_size'], result['rank_checks'],
     result['full_automorphism_counts'])=test_relations()
    result['minor_constructions']=test_minor_universality()
    result['vertex_sum_identities'],result['theta_certificate']=test_gluing_and_witness()
    result['elapsed_seconds']=round(time.perf_counter()-start,3)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
