#!/usr/bin/env python3
"""Exact, self-contained certificates for Report 232 (Python standard library).

All comparisons use explicit exceptions, including under python -O. No numerical
fit or third-party computer-algebra package is used. Polynomials are ascending
rational coefficient tuples. This file never writes to its source directory.
"""
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def add(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a): c[i] += x
    for i, x in enumerate(b): c[i] += x
    while len(c) > 1 and c[-1] == 0: c.pop()
    return tuple(c)


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    while len(c) > 1 and c[-1] == 0: c.pop()
    return tuple(c)


def evaluate(p, n):
    answer = F(0)
    for a in reversed(p): answer = answer*n + a
    return answer


def dense_edges(edges):
    vertices = sorted({a for e in edges for a in e[:2]})
    index = {a:i for i,a in enumerate(vertices)}
    return tuple(sorted((min(index[a],index[b]),max(index[a],index[b]),c)
                        for a,b,c in edges))


@lru_cache(None)
def canonical_connected(edges):
    edges = dense_edges(edges)
    size = 1+max(b for a,b,c in edges)
    best, aut = None, 0
    for p in permutations(range(size)):
        candidate = tuple(sorted((min(p[a],p[b]),max(p[a],p[b]),c)
                                 for a,b,c in edges))
        if best is None or candidate < best:
            best, aut = candidate, 1
        elif candidate == best:
            aut += 1
    return (size, best), aut


def canonical(edges):
    vertices = {a for edge in edges for a in edge[:2]}
    components, aut = [], 1
    while vertices:
        reached = {min(vertices)}
        while True:
            new = reached | {b for a,b,c in edges if a in reached} | {a for a,b,c in edges if b in reached}
            if new == reached: break
            reached = new
        local = dense_edges(tuple(e for e in edges if e[0] in reached))
        component, a = canonical_connected(local)
        components.append(component)
        aut *= a
        vertices -= reached
    for multiplicity in Counter(components).values(): aut *= factorial(multiplicity)
    return tuple(sorted(components)), aut


def flatten(graph, R, reverse=False):
    result, offset = [], 0
    for size, edges in graph:
        result.extend((a+offset,b+offset,(R,1)[c] if reverse else (1,R)[c])
                      for a,b,c in edges)
        offset += size
    return offset, tuple(result)


def swapped(graph):
    edges, offset = [], 0
    for size, local in graph:
        edges.extend((a+offset,b+offset,1-c) for a,b,c in local)
        offset += size
    return canonical(tuple(edges))[0]


def edge_degree(graph):
    return sum(len(e) for v,e in graph)


def catalogue(R):
    """Grow every connected selected graph by an adjacent edge, then multisets."""
    levels = {1:{((0,1,0),), ((0,R,1),)}}
    components = {}
    for degree in range(1,5):
        for edges in sorted(levels[degree]):
            component, aut = canonical_connected(dense_edges(edges))
            components[component] = aut
        if degree == 4: break
        next_level = set()
        for edges in levels[degree]:
            vertices = {a for e in edges for a in e[:2]}
            for x in vertices:
                for color, gap in enumerate((1,R)):
                    for y in (x-gap,x+gap):
                        extra = (min(x,y),max(x,y),color)
                        if extra in edges: continue
                        new = tuple(sorted(edges+(extra,)))
                        low = min(a for a,b,c in new)
                        next_level.add(tuple((a-low,b-low,c) for a,b,c in new))
        levels[degree+1] = next_level
    ordered = sorted(components)
    result = {}
    def rec(first, graph, total):
        if graph:
            aut = 1
            for g in graph: aut *= components[g]
            for multiplicity in Counter(graph).values(): aut *= factorial(multiplicity)
            result[graph] = aut
        for i in range(first,len(ordered)):
            component = ordered[i]
            if total+len(component[1]) <= 4:
                rec(i,graph+(component,),total+len(component[1]))
    rec(0,(),0)
    require(len(result) == {2:87,3:83}[R], 'Unexpected complete catalogue size')
    return result


@lru_cache(None)
def partitions(size):
    if size == 0: return ((),)
    if size == 1: return ((0,),)
    return tuple(p+(b,) for p in partitions(size-1) for b in range(max(p)+2))


@lru_cache(None)
def hom_polynomial(size, constraints):
    if any(a == b for a,b,d in constraints): return (F(0),)
    length = {}
    for a,b,d in constraints:
        edge = (min(a,b),max(a,b))
        if edge in length and length[edge] != d: return (F(0),)
        length[edge] = d
    edges = tuple((a,b,d) for (a,b),d in sorted(length.items()))
    unused, polynomial = set(range(size)), (F(1),)
    while unused:
        root = min(unused)
        seen, tree, queue = {root}, [], [root]
        for a in queue:
            for x,y,d in edges:
                b = y if x == a else x if y == a else None
                if b is not None and b not in seen:
                    seen.add(b); queue.append(b); tree.append((a,b,d))
        unused -= seen
        slope, intercept = 0, 0
        for signs in product((-1,1),repeat=len(tree)):
            coordinates = {root:0}
            for (a,b,d),sign in zip(tree,signs): coordinates[b] = coordinates[a]+sign*d
            if all(abs(coordinates[a]-coordinates[b]) == d for a,b,d in edges if a in seen):
                slope += 1
                intercept -= max(coordinates.values())-min(coordinates.values())
        polynomial = mul(polynomial,(F(intercept),F(slope)))
    return polynomial


def injection_polynomial(size, constraints):
    result = (F(0),)
    for p in partitions(size):
        sizes = Counter(p)
        mobius = 1
        for value in sizes.values(): mobius *= (-1)**(value-1)*factorial(value-1)
        quotient = tuple(sorted({(min(p[a],p[b]),max(p[a],p[b]),d) for a,b,d in constraints}))
        polynomial = hom_polynomial(len(sizes),quotient)
        result = add(result,tuple(mobius*a for a in polynomial))
    return result


def graph_counts(n,R):
    edges = [(i,i+d,c) for c,d in enumerate((1,R)) for i in range(max(0,n-d))]
    answer, automorphisms = Counter(), {}
    for degree in range(1,5):
        for selected in combinations(edges,degree):
            graph, aut = canonical(selected)
            answer[graph] += 1
            automorphisms[graph] = aut
    return answer, automorphisms


def correction_polynomials(rows):
    """Compute e^(-2u-2v)G through n^-2 and marked degree four."""
    pgf = defaultdict(F)
    pgf[0,0,0] = F(1)
    for row in rows:
        graph, aut, source, target = row
        vertices = sum(size for size,e in graph)
        ka = sum(c == 0 for size,es in graph for a,b,c in es)
        kb = edge_degree(graph)-ka
        numerator = tuple(aut*a for a in mul(source,target))
        require(len(numerator)-1 <= vertices,'Negative graph deficit')
        S1 = F(vertices*(vertices-1),2)
        S2 = F(vertices*(vertices-1)*(2*vertices-1),6)
        den = (F(1),S1,(S1*S1+S2)/2)
        for power,coefficient in enumerate(numerator):
            deficit = vertices-power
            for j in range(3):
                if 0 <= deficit+j <= 2: pgf[ka,kb,deficit+j] += coefficient*den[j]
    result = defaultdict(F)
    for (ka,kb,j),value in pgf.items():
        for a in range(5-ka-kb):
            for b in range(5-ka-kb-a):
                result[ka+a,kb+b,j] += value*F((-2)**(a+b),factorial(a)*factorial(b))
    return {key:value for key,value in result.items() if value}


def expected_corrections(R):
    answer = {(0,0,0):F(1),(1,0,1):F(-2*R),(0,1,1):F(-2*R),
              (2,0,1):F(-2),(0,2,1):F(-2)}
    for a,b,value in [(4,0,2),(0,4,2),(3,0,4*R+2),(0,3,4*R+2),
                      (2,0,12*R-14),(0,2,12*R-14),(2,2,8),
                      (2,1,8*R-12),(1,2,8*R-12),(1,1,20*R-16)]:
        answer[a,b,2] = F(value)
    return answer


def distribution(n,R):
    result = Counter()
    for p in permutations(range(n)):
        x = sum(abs(p[i+1]-p[i]) == R for i in range(max(0,n-1)))
        y = sum(abs(p[i+R]-p[i]) == 1 for i in range(max(0,n-R)))
        result[x,y] += 1
    require(sum(result.values()) == factorial(n),'Permutation total')
    return result


def actual_moment_numerators(hist):
    result = Counter()
    for (x,y),count in hist.items():
        for a in range(min(4,x)+1):
            for b in range(min(4-a,y)+1):
                if a+b: result[a,b] += count*comb(x,a)*comb(y,b)
    return result


def event_moment_numerators(n,R):
    counts, aut = graph_counts(n,R)
    result = Counter()
    for graph,number in counts.items():
        size = sum(v for v,e in graph)
        ka = sum(c == 0 for v,es in graph for a,b,c in es)
        kb = edge_degree(graph)-ka
        result[ka,kb] += aut[graph]*number*counts.get(swapped(graph),0)*factorial(n-size)
    return +result


def polynomial_moment_numerators(n,rows):
    result = defaultdict(F)
    for graph,aut,source,target in rows:
        size = sum(v for v,e in graph)
        require(size <= n,'Moment denominator unsupported at this n')
        ka = sum(c == 0 for v,es in graph for a,b,c in es)
        kb = edge_degree(graph)-ka
        result[ka,kb] += aut*evaluate(source,n)*evaluate(target,n)*factorial(n-size)
    return dict(result)


def plus(exponent,position):
    value = list(exponent); value[position] += 1
    return tuple(value)


def packing_transfer(n,species,cutoff=4):
    types = 1+max(t for P,t in species)
    states = {(0,(0,)*types):1}
    for site in range(n):
        updated = defaultdict(int)
        for (mask,exponent),weight in states.items():
            updated[mask>>1,exponent] += weight
            if mask&1 or sum(exponent) == cutoff: continue
            for support,t in species:
                occupied = sum(1<<i for i in support)
                if not mask&occupied:
                    updated[(mask|occupied)>>1,plus(exponent,t)] += weight
        states = updated
    return Counter({ex:weight for (mask,ex),weight in states.items() if mask == 0})


def packing_direct(n,species,cutoff=4):
    """Independent placement-subset recursion; no scan or transfer state."""
    types = 1+max(t for P,t in species)
    placements = [(sum(1<<(i+a) for i in support),t)
                  for support,t in species for a in range(max(0,n-max(support)))]
    answer = Counter()
    def rec(start,occupied,exponent):
        answer[exponent] += 1
        if sum(exponent) == cutoff: return
        for i in range(start,len(placements)):
            mask,t = placements[i]
            if not mask&occupied: rec(i+1,mask|occupied,plus(exponent,t))
    rec(0,0,(0,)*types)
    return answer


def packing_checks():
    dictionaries = [[((0,1),0),((0,3),1),((0,1,3),2),((0,2,3),2),((0,1,3,4),3)],
                    [((0,2),0),((0,2),1),((0,1,3),2),((0,2,3),3)]]
    for dictionary in dictionaries:
        for n in range(10):
            require(packing_transfer(n,dictionary) == packing_direct(n,dictionary),
                    'Transfer/direct packing mismatch')
    require(packing_transfer(4,[((0,3),0),((0,1),1)])[(1,1)] == 1,'Interlacing test')
    return {'comparisons':20,'n_range':[0,9],'polymer_cutoff':4,'interlacing':True,
            'duplicate_supports':True,'shared_types':True,'right_boundary':True}


def fraction_text(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else f'{value.numerator}/{value.denominator}'


def exact_json():
    output = {'format':'report232-exact-v1','packing':packing_checks(),'models':{}}
    for R in (2,3):
        cat = catalogue(R)
        rows, encoded = [], []
        for graph,aut in sorted(cat.items()):
            size,edges = flatten(graph,R)
            source = tuple(a/aut for a in injection_polynomial(size,edges))
            _,edges = flatten(graph,R,True)
            target = tuple(a/aut for a in injection_polynomial(size,edges))
            rows.append((graph,aut,source,target))
            encoded.append({'graph':graph,'automorphisms':aut,
                            'source':[fraction_text(a) for a in source],
                            'target':[fraction_text(a) for a in target]})
        corrections = correction_polynomials(rows)
        require(corrections == expected_corrections(R),'Full correction polynomial mismatch')
        # Separate direct selected-edge enumeration checks eventual polynomials.
        for n in (4*R,4*R+1,16):
            counts, _ = graph_counts(n,R)
            require(set(counts) <= set(cat),'Missing graph type in catalogue')
            if n == 16: require(set(counts) == set(cat),'Catalogue completeness at n=16')
            for graph,aut,source,target in rows:
                require(evaluate(source,n) == counts[graph],'Source polynomial certificate')
                require(evaluate(target,n) == counts.get(swapped(graph),0),'Target polynomial certificate')
        small = {}
        for n in range(4,10):
            hist = distribution(n,R)
            actual = actual_moment_numerators(hist)
            require(actual == event_moment_numerators(n,R),'Independent permutation/event moments')
            S = 4*n-4*R-2
            D = (n-1)*(n-R)-S
            if n >= R+1:
                require(actual[1,0] == 2*(n-1)*(n-R)*factorial(n-2),'First moment')
                require(actual.get((1,1),0) == S*S*factorial(n-3)+4*D*D*factorial(n-4),'Mixed moment')
            small[str(n)] = {'avoidance':hist[0,0],
                             'distribution':{f'{x},{y}':count for (x,y),count in sorted(hist.items())},
                             'binomial_moment_numerators':{f'{a},{b}':count for (a,b),count in sorted(actual.items())}}
        require(small['9']['avoidance'] == {2:19480,3:22854}[R],'n=9 avoidance reference')
        actual4 = 24*sum(value for key,value in actual.items() if sum(key) == 4)
        eventual = polynomial_moment_numerators(9,rows)
        eventual4 = 24*sum(value for key,value in eventual.items() if sum(key) == 4)
        if R == 3:
            require(actual4 == 12829728 and eventual4 == 13044000,'Camel boundary counterexample')
        else:
            require(actual4 == eventual4,'Knight fourth moment at certified n')
        avoidance = [sum(value*(-1)**(a+b) for (a,b,k),value in corrections.items() if k == j)
                     for j in range(3)]
        require(avoidance == [1,4 if R == 2 else 8,28 if R == 2 else 48],'Avoidance corrections')
        output['models'][str(R)] = {'safe_polynomial_threshold':4*R,'graph_count':len(rows),
            'graph_certificates':encoded,
            'corrections':{f'{a},{b},{j}':fraction_text(value) for (a,b,j),value in sorted(corrections.items())},
            'avoidance_coefficients':[fraction_text(value) for value in avoidance],
            'small_n':small,'n9_fourth_falling_moment_numerator':actual4,
            'n9_eventual_fourth_falling_moment_numerator':fraction_text(eventual4)}
    return json.dumps(output,sort_keys=True,indent=2)+'\n'


if __name__ == '__main__':
    require(len(sys.argv) == 1,'This checker takes no arguments; use build.py --output NEW_DIRECTORY')
    sys.stdout.write(exact_json())
