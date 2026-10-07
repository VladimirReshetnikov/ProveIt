#!/usr/bin/env python3
"""Exact, deterministic checks for Sparse Grid Moments and Quadratic Closure.

Uses Python 3.10+ and the standard library only. This is a reproducibility
check, not a Lean formalization. The article proves the general formulas.

Default: all matrices in the seven-dimensional cube space over F_2,F_3,
F_4,F_5; all subsets of the binary 3-cube over those fields; and independent
small direct-count and polynomial-coefficient checks.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
from typing import Iterable, Sequence


@dataclass(frozen=True)
class Field:
    order: int
    characteristic: int
    modulus: int | None = None

    @classmethod
    def create(cls, order: int) -> 'Field':
        if order in (4, 8):
            return cls(order, 2, {4: 0b111, 8: 0b1011}[order])
        if order >= 2 and all(order % i for i in range(2, int(order**0.5) + 1)):
            return cls(order, order)
        raise ValueError('Supported orders: primes, 4, and 8.')

    def add(self, a: int, b: int) -> int:
        return a ^ b if self.modulus is not None else (a + b) % self.order

    def neg(self, a: int) -> int:
        return a if self.characteristic == 2 else (-a) % self.order

    def sub(self, a: int, b: int) -> int:
        return self.add(a, self.neg(b))

    def mul(self, a: int, b: int) -> int:
        if self.modulus is None:
            return (a * b) % self.order
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & self.order:
                a ^= self.modulus
        return result

    def power(self, a: int, k: int) -> int:
        out = 1
        while k:
            if k & 1:
                out = self.mul(out, a)
            a = self.mul(a, a)
            k >>= 1
        return out

    def inv(self, a: int) -> int:
        if a == 0:
            raise ZeroDivisionError('Zero has no inverse in a field.')
        return self.power(a, self.order - 2)


def rank(matrix: Sequence[Sequence[int]], field: Field) -> int:
    if not matrix:
        return 0
    a = [list(row) for row in matrix]
    width = len(a[0])
    if any(len(row) != width for row in a):
        raise ValueError('Ragged matrix.')
    r = 0
    for j in range(width):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inverse = field.inv(a[r][j])
        a[r] = [field.mul(x, inverse) for x in a[r]]
        for i in range(r + 1, len(a)):
            c = a[i][j]
            if c:
                a[i] = [field.sub(x, field.mul(c, y)) for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def cube_matrix(t: Sequence[int]) -> list[list[int]]:
    a, b, c, d, e, f, g = t
    return [[a,b,c,d], [b,b,e,f], [c,e,c,g], [d,f,g,d]]


def cube_rank_formula(field: Field) -> list[int]:
    q = field.order
    if field.characteristic == 2:
        return [1, 8*(q-1), (q-1)*(q**3+8*q**2+q-7),
                q**2*(q-1)*(q**3+q**2+8*q-14),
                q**2*(q-1)**2*(q**3+q**2+q-7)]
    return [1, 8*(q-1), (q-1)*(q**3+7*q**2+q-7),
            q**2*(q-1)*(q**3+q**2+7*q-13),
            q**2*(q-1)*(q**4-7*q+7)]


def enumerate_cube_ranks(field: Field) -> list[int]:
    counts = [0]*5
    # No use of the closed formulas in this enumeration.
    for t in product(range(field.order), repeat=7):
        counts[rank(cube_matrix(t), field)] += 1
    expected = cube_rank_formula(field)
    assert counts == expected, (field.order, counts, expected)
    assert sum(counts) == field.order**7
    return counts


def margin_matrix(sites: Sequence[tuple[int, ...]], sizes: Sequence[int], degree: int) -> list[list[int]]:
    rows = []
    for j in range(min(degree, len(sizes))+1):
        for axes in combinations(range(len(sizes)), j):
            for labels in product(*(range(sizes[i]) for i in axes)):
                rows.append([int(tuple(site[i] for i in axes) == labels) for site in sites])
    return rows


def full_grid_formula(sizes: Sequence[int], degree: int) -> int:
    total = 0
    for j in range(min(degree, len(sizes))+1):
        for axes in combinations(range(len(sizes)), j):
            term = 1
            for i in axes:
                term *= sizes[i]-1
            total += term
    return total


def grid_rank_checks(fields: Sequence[Field]) -> list[dict]:
    records = []
    for field in fields:
        for sizes in [(2,2,2), (2,3,2), (3,3), (2,2,2,2)]:
            sites = list(product(*(range(m) for m in sizes)))
            for d in range(0, len(sizes)+1):
                actual = rank(margin_matrix(sites, sizes, d), field)
                expected = full_grid_formula(sizes, d)
                assert actual == expected
                records.append({'Q': field.order, 'sizes': sizes, 'degree': d, 'rank': actual})
    return records


def feature(site: tuple[int, ...]) -> list[int]:
    a,b,c = site
    return [1,a,b,c,a*b,a*c,b*c]


def all_cube_subsets(field: Field) -> dict:
    sites = list(product(range(2), repeat=3))
    all_features = [feature(site) for site in sites]
    histogram = Counter()
    for mask in range(1, 256):
        chosen = [i for i in range(8) if (mask >> i) & 1]
        basis = [all_features[i] for i in chosen]
        r = rank(basis, field)
        closure = sum(rank(basis+[v], field) == r for v in all_features)
        size = len(chosen)
        # A ternary-grid check below separately checks the representation.
        assert r == (7 if size == 8 else size)
        assert closure == (8 if size >= 7 else size)
        histogram[(size,r,closure)] += 1
    return {'Q': field.order, 'subsets_checked': 255,
            'profiles': [{'size': key[0], 'rank': key[1], 'closure': key[2], 'count': value}
                         for key,value in sorted(histogram.items())]}


def one_hot(site: tuple[int,...], sizes: Sequence[int]) -> list[int]:
    return [int(site[a] == b) for a in range(len(sizes)) for b in range(sizes[a])]


def symmetric_feature(site: tuple[int,...], sizes: Sequence[int]) -> list[int]:
    v = one_hot(site, sizes)
    return [v[i]*v[j] for i in range(len(v)) for j in range(i, len(v))]


def general_pattern_checks(fields: Sequence[Field]) -> list[dict]:
    sizes = (2,3,2)
    full = list(product(*(range(m) for m in sizes)))
    # Deterministic nonexhaustive patterns, not a probabilistic test.
    patterns = [full[:k] for k in range(1, len(full)+1)]
    patterns += [full[::2], full[1::2], [s for s in full if s[1] != 1]]
    out = []
    for f in fields:
        for sites in patterns:
            r1 = rank(margin_matrix(sites, sizes, 2), f)
            r2 = rank([symmetric_feature(s, sizes) for s in sites], f)
            assert r1 == r2
            out.append({'Q': f.order, 'size': len(sites), 'rank': r1})
    return out


def direct_zero_count(field: Field, size: int) -> dict:
    """Independent enumeration of two vectors in F^4, n=1, on cube sites.

    The representative (base, increments) has the correct uniform law:
    base is the sum of the three independent base-axis inputs.
    """
    sites = list(product(range(2), repeat=3))[:size]
    q = field.order
    zero_count = 0
    vectors = list(product(range(q), repeat=4))
    site_values = []
    for x in vectors:
        values = []
        for site in sites:
            total = x[0]
            for j, bit in enumerate(site):
                if bit:
                    total = field.add(total, x[j+1])
            values.append(total)
        site_values.append(values)
    for xs in site_values:
        for ys in site_values:
            if all(field.mul(x,y) == 0 for x,y in zip(xs,ys)):
                zero_count += 1
    raw = Fraction(q**size * zero_count, q**8)
    counts = cube_rank_formula(field)
    z = Fraction(1,q)
    rank_poly = sum(counts[h]*z**h for h in range(5))
    expected = (q if size == 8 else 1)*rank_poly
    assert raw == expected
    normalized = raw / (1+(q-1)*z)**size
    return {'Q': q, 'sites': size, 'input_pairs': q**8, 'zero_pairs': zero_count,
            'raw_moment': str(raw), 'normalized_moment': str(normalized)}


def polynomial_product(a: dict[tuple[int,...],int], b: dict[tuple[int,...],int], p: int) -> dict:
    out: dict[tuple[int,...],int] = {}
    for ma,ca in a.items():
        for mb,cb in b.items():
            key = tuple(x+y for x,y in zip(ma,mb))
            out[key] = (out.get(key,0)+ca*cb) % p
    return {key:value for key,value in out.items() if value}


def polynomial_relation_check(p: int, sizes: Sequence[int],
                              monomials: Sequence[tuple[tuple[int,...],int]]) -> dict:
    """Check equality of kernels via ranks of stacked coefficient matrices.

    Expansion is independent of margin-matrix construction. Formal monomial
    coefficients use only exact modular arithmetic.
    """
    f = Field.create(p)
    sites = list(product(*(range(m) for m in sizes)))
    e = len(monomials[0][0])
    d = max(sum(exponents) for exponents, coefficient in monomials if coefficient % p)
    variables = e*sum(sizes)
    zero = (0,)*variables
    offsets = [sum(sizes[:i]) for i in range(len(sizes))]
    polys = []
    for site in sites:
        poly: dict[tuple[int,...],int] = {}
        for exponents,coefficient in monomials:
            term = {zero: coefficient % p}
            for r,power in enumerate(exponents):
                linear = {}
                for axis,b in enumerate(site):
                    index = e*(offsets[axis]+b)+r
                    key = list(zero); key[index] = 1
                    linear[tuple(key)] = 1
                for _ in range(power):
                    term = polynomial_product(term, linear, p)
            for key,value in term.items():
                poly[key] = (poly.get(key,0)+value) % p
        polys.append(poly)
    keys = sorted(set().union(*(set(poly) for poly in polys)))
    coeffs = [[poly.get(key,0) for poly in polys] for key in keys]
    top_coeffs = [row for key,row in zip(keys,coeffs) if sum(key) == d]
    margins = margin_matrix(sites,sizes,d)
    r = rank(margins,f)
    assert rank(coeffs,f) == r
    assert rank(top_coeffs,f) == r
    assert rank(coeffs+margins,f) == r
    assert rank(top_coeffs+margins,f) == r
    return {'p':p, 'sizes':sizes, 'base_variables':e, 'degree':d, 'sites':len(sites),
            'coefficient_rows':len(keys), 'rank':r}


def support_check() -> dict:
    # Over F2, all 16 coefficient vectors for d=1 on a 2x2 grid,
    # and all 256 for d=2 on a 2x2x2 grid.
    reports=[]
    for sizes,d in [((2,2),1),((2,2,2),2),((2,2,2,2),2)]:
        sites=list(product(*(range(m) for m in sizes)))
        rows=margin_matrix(sites,sizes,d)
        row_masks=[sum(x<<i for i,x in enumerate(row)) for row in rows]
        minimum=None; words=0
        for mask in range(1,1<<len(sites)):
            if all((mask&row_mask).bit_count()%2 == 0 for row_mask in row_masks):
                words+=1
                support=mask.bit_count()
                minimum=support if minimum is None else min(minimum,support)
        assert minimum == 2**(d+1)
        reports.append({'sizes':sizes,'degree':d,'nonzero_relations':words,'minimum_support':minimum})
    return {'field':2,'checks':reports}


def is_forest(edges: Sequence[tuple[int,int]], vertices: int) -> bool:
    parent=list(range(vertices))
    def root(x: int) -> int:
        while parent[x] != x:
            x=parent[x]
        return x
    for u,v in edges:
        ru,rv=root(u),root(v)
        if ru == rv:
            return False
        parent[ru]=rv
    return True


def graph_girth(edges: Sequence[tuple[int,int]], vertices: int) -> int | None:
    from collections import deque
    adjacency=[[] for _ in range(vertices)]
    for i,(u,v) in enumerate(edges):
        adjacency[u].append((v,i)); adjacency[v].append((u,i))
    best=None
    for omitted,(start,target) in enumerate(edges):
        distance={start:0}; queue=deque([start])
        while queue:
            u=queue.popleft()
            for v,index in adjacency[u]:
                if index == omitted or v in distance:
                    continue
                distance[v]=distance[u]+1
                queue.append(v)
        if target in distance:
            length=distance[target]+1
            best=length if best is None else min(best,length)
    return best


def count_cycles_of_length(edges: Sequence[tuple[int,int]], vertices: int, length: int) -> int:
    adjacency=[[] for _ in range(vertices)]
    for u,v in edges:
        adjacency[u].append(v);adjacency[v].append(u)
    count=0
    def visit(start: int, path: list[int]) -> None:
        nonlocal count
        u=path[-1]
        if len(path) == length:
            if start in adjacency[u]:
                count+=1
            return
        for v in adjacency[u]:
            if v>start and v not in path:
                visit(start,path+[v])
    for start in range(vertices):
        visit(start,[start])
    assert count%2 == 0
    return count//2


def graph_checks() -> list[dict]:
    from math import comb
    patterns=[]
    for length in (4,6,8):
        m=length//2
        sites=[(i,i) for i in range(m)]+[(i,(i-1)%m) for i in range(m)]
        patterns.append((f'C{length}',(m,m),sites,True))
    patterns += [
        ('K2,3',(2,3),list(product(range(2),range(3))),False),
        ('K3,3',(3,3),list(product(range(3),range(3))),False),
        ('path5',(3,3),[(0,0),(1,0),(1,1),(2,1),(2,2)],False)]
    results=[]
    for q in (2,3):
        f=Field.create(q)
        for name,sizes,sites,is_cycle in patterns:
            s=len(sites);vertices=sum(sizes)
            edges=[(u,sizes[0]+v) for u,v in sites]
            girth=graph_girth(edges,vertices)
            counts=[0]*(max(vertices,s)+1)
            for weights in product(range(q),repeat=s):
                active=[edge for edge,w in zip(edges,weights) if w]
                mat=[[0]*vertices for _ in range(vertices)]
                for (u,v),w in zip(edges,weights):
                    if w:
                        mat[u][u]=f.add(mat[u][u],w)
                        mat[v][v]=f.add(mat[v][v],w)
                        mat[u][v]=f.sub(mat[u][v],w)
                        mat[v][u]=f.sub(mat[v][u],w)
                r=rank(mat,f)
                counts[r]+=1
                if is_forest(active,vertices):
                    assert r == len(active)
                else:
                    assert girth is not None
                    assert girth-2 <= r < len(active)
            baseline=[comb(s,h)*(q-1)**h if h<=s else 0 for h in range(len(counts))]
            difference=[x-y for x,y in zip(counts,baseline)]
            if girth is None:
                assert not any(difference)
                leading=None;coefficient=0;shortest_cycles=0
            else:
                leading=next(i for i,value in enumerate(difference) if value)
                coefficient=difference[leading]
                assert leading == girth-2 and coefficient>0
                shortest_cycles=count_cycles_of_length(edges,vertices,girth)
                cycle_zero=((q-1)**girth+(q-1))//q
                assert coefficient >= shortest_cycles*cycle_zero
            if is_cycle:
                zero=((q-1)**s+(q-1))//q
                expected=baseline.copy()
                expected[s-2]+=zero
                expected[s-1]+=(q-1)**s-zero
                expected[s]-=(q-1)**s
                assert counts == expected
                assert coefficient == zero
            z=Fraction(1,q)
            moment=sum(value*z**h for h,value in enumerate(counts))/(1+(q-1)*z)**s
            assert (moment == 1) if girth is None else (moment>1)
            results.append({'Q':q,'pattern':name,'sites':s,'frequencies_checked':q**s,
                'girth':girth,'shortest_cycles':shortest_cycles,'rank_counts':counts,
                'first_error_degree':leading,'leading_coefficient':coefficient,
                'normalized_moment_n1':str(moment)})
    return results


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fields',default='2,3,4,5',help='Comma-separated field orders; 7 and 8 are optional larger checks.')
    parser.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=parser.parse_args()
    fields=[Field.create(int(q)) for q in args.fields.split(',')]
    results: dict = {'status':'passed','arithmetic':'exact; no floating-point tests',
                     'scope':'finite verification only; general theorems have written proofs',
                     'rank_enumerators':[]}
    for f in fields:
        counts=enumerate_cube_ranks(f)
        print(f'F_{f.order}: {counts}',flush=True)
        results['rank_enumerators'].append({'Q':f.order,'characteristic':f.characteristic,
            'matrices_checked':f.order**7,'rank_counts':counts,
            'second_normalized_coefficient':counts[2]-28*(f.order-1)**2})
    results['full_grid_ranks']=grid_rank_checks(fields)
    results['cube_subset_closure']=[all_cube_subsets(f) for f in fields]
    results['general_pattern_representation']=general_pattern_checks(fields)
    results['direct_moments']=[direct_zero_count(Field.create(q),s) for q in (2,3) for s in (7,8)]
    results['polynomial_relations']=[
        polynomial_relation_check(2,(2,2,2,2),[((1,1,1),1),((1,0,0),1),((0,0,0),1)]),
        polynomial_relation_check(3,(2,2,2),[((2,),1),((1,),2),((0,),1)]),
        polynomial_relation_check(3,(2,2,2),[((2,1),1),((0,2),2),((0,0),1)])]
    results['minimum_support']=support_check()
    results['graph_girth_and_cycles']=graph_checks()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(results,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(f'All checks passed. Results: {args.output}',flush=True)


if __name__ == '__main__':
    main()
