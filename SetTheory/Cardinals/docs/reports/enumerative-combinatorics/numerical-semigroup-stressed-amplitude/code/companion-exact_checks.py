#!/usr/bin/env python3
"""Independent, bounded, exact diagnostics for Report 274.

These finite checks are not proofs of the infinite-length estimates.  No floating
point arithmetic, empirical amplitude, root approximation, or audit code is used.
All exported enumeration inputs have explicit caps, including under python -O.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
from math import comb, isqrt
import json
import re

DIGIT_CAP = 640
MAX_LENGTH = 12
MAX_BOUNDARY = 10
MAX_GRAPH = 9
MAX_ALLOCATION = 8
MAX_STRUCTURE = 256


class CheckFailure(RuntimeError):
    """A failed diagnostic; explicit rather than optimization-removable asserts."""


def ensure(condition, message):
    if not condition:
        raise CheckFailure(message)


def bounded_int(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in [{low}, {high}]")
    return value


def parse_integer(text, name, low, high):
    if not isinstance(text, str) or not 1 <= len(text) <= DIGIT_CAP:
        raise ValueError(f"{name}: expected at most {DIGIT_CAP} ASCII digits")
    if re.fullmatch(r"[0-9]+", text) is None:
        raise ValueError(f"{name}: expected ASCII decimal integer")
    # The magnitude check precedes conversion, even if the interpreter digit
    # limit has been disabled by a caller or an unusual Python implementation.
    canonical = text.lstrip("0") or "0"
    if len(canonical) > len(str(high)):
        raise ValueError(f"{name} is outside the bounded range")
    return bounded_int(int(canonical), name, low, high)


def checked_activities(values):
    if not isinstance(values, (tuple, list)) or len(values) != 3:
        raise ValueError("three exact positive activities required")
    out = []
    for value in values:
        if type(value) not in (int, Q):
            raise ValueError("activities must be integers or Fractions")
        value = Q(value)
        if not 0 < value <= 16 or max(value.numerator.bit_length(), value.denominator.bit_length()) > 128:
            raise ValueError("activity exceeds exact-arithmetic input cap")
        out.append(value)
    return tuple(out)


# Dense tuples of coefficients: the index is the genus, all coefficients are
# integers.  Polynomial utilities are internal and receive only bounded data.
def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def _add(p, q):
    r = [0] * max(len(p), len(q))
    for i, x in enumerate(p):
        r[i] += x
    for i, x in enumerate(q):
        r[i] += x
    return _trim(r)


def _mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                if y:
                    r[i+j] += x*y
    return _trim(r)


def _power(p, n):
    r = (1,)
    for _ in range(n):
        r = _mul(r, p)
    return r


def _shift(p, n):
    return (0,) * n + p


A_POLY = (0, 0, 1, 1)
B_POLY = (0, 1, 1, 1)
C_POLY = (0, 1, 1)
P_POLY = _mul(A_POLY, B_POLY)


def stressed(word):
    if not isinstance(word, (tuple, list)) or not 1 <= len(word) <= MAX_LENGTH:
        raise ValueError("word length outside diagnostic cap")
    if any(type(x) is not int or x not in (1, 2, 3) for x in word):
        raise ValueError("word letters must be 1, 2, or 3")
    if word[-1] != 3:
        return False
    # Check the full original unwrapped inequalities, including repeated inputs.
    return all(word[i-1] + word[j-1] >= word[i+j-1]
               for i in range(1, len(word)+1)
               for j in range(i, len(word)-i+1))


@lru_cache(maxsize=MAX_LENGTH)
def _words(length):
    return tuple(w for prefix in product((1, 2, 3), repeat=length-1)
                 if stressed(w := prefix + (3,)))


def stressed_words(length):
    bounded_int(length, "length", 1, MAX_LENGTH)
    return _words(length)


def _histogram(words):
    counts = Counter(map(sum, words))
    result = [0] * (max(counts, default=0)+1)
    for genus, count in counts.items():
        result[genus] = count
    return _trim(result)


def genus_polynomial(length, separated=False):
    bounded_int(length, "length", 1, MAX_LENGTH)
    if type(separated) is not bool:
        raise ValueError("separated must be boolean")
    words = stressed_words(length)
    if separated:
        words = [w for w in words if all(w[i-1] != 1 for i in range(1, length//3+1))]
    return _histogram(words)


def _boundary_sets(r):
    for mask in range(1 << (r-1)):
        selected = (0,) + tuple(j for j in range(1, r) if mask & (1 << (j-1)))
        sums = {i+j for i in selected for j in selected}
        if r not in sums:
            yield selected, len(sums.intersection(range(r)))


def boundary_polynomial(r):
    bounded_int(r, "boundary length", 1, MAX_BOUNDARY)
    total = (0,)
    for selected, covered in _boundary_sets(r):
        term = _mul(_power(A_POLY, 2*r+1-len(selected)),
                    _mul(_power(C_POLY, covered), _power(B_POLY, r-covered)))
        total = _add(total, _shift(term, len(selected)+3))
    return total


def transformed_boundary_polynomial(r):
    bounded_int(r, "boundary length", 1, MAX_BOUNDARY)
    # A * sum (A^2)^n1 (A^2 C)^n2 (A^2 x^3)^n3,
    # enumerated from the original inequalities, not from boundary sets.
    signatures = Counter((w.count(2), w.count(3)) for w in stressed_words(r))
    inside = (0,)
    for (twos, threes), count in signatures.items():
        term = _shift(tuple(count*x for x in _power(C_POLY, twos)), 3*threes)
        inside = _add(inside, term)
    return _mul(_power(A_POLY, 2*r+1), inside)


def renewal_polynomial(length):
    bounded_int(length, "length", 1, MAX_LENGTH)
    if length % 2:
        result = _shift(_power(P_POLY, (length-1)//2), 3)
    else:
        result = _shift(_mul(A_POLY, _power(P_POLY, (length-2)//2)), 3)
    for r in range(1, (length-2)//3+1):
        rest = length-(3*r+2)
        if rest >= 0 and rest % 2 == 0:
            result = _add(result, _mul(boundary_polynomial(r), _power(P_POLY, rest//2)))
    return result


def activity_partition(length, activities):
    bounded_int(length, "length", 1, MAX_LENGTH)
    u, v, w = checked_activities(activities)
    signatures = Counter((s.count(1), s.count(2), s.count(3)) for s in stressed_words(length))
    return sum((count*u**a*v**b*w**c for (a,b,c), count in signatures.items()), Q(0))


def general_boundary(r, activities):
    bounded_int(r, "boundary length", 1, MAX_BOUNDARY)
    u, v, w = checked_activities(activities)
    a, b, c = v+w, u+v+w, u+v
    return sum((a**r*u**len(j)*w*a**(r+1-len(j))*c**cover*b**(r-cover)
                for j, cover in _boundary_sets(r)), Q(0))


def activity_transform(activities):
    u, v, w = checked_activities(activities)
    a, c = v+w, u+v
    return u*a*c, a*a*c, a*a*w


def pair_factors(activities):
    u, v, w = checked_activities(activities)
    b, c = v+w, u+v
    return {"P": b*(b+u), "T": v*v+2*u*v,
            "E_squared": (b*c)**2*(b+2*u)/(b+u),
            "L1": (b+u)/b, "L2": (b+2*u)/(b+u), "Lb": (b*c+u*v)/(b*c)}


def eligibility_checks(max_pairs):
    bounded_int(max_pairs, "allocation size", 0, MAX_ALLOCATION)
    triples = ((Q(1,2),Q(1,3),Q(1,5)), (Q(3,2),Q(4,3),Q(2,5)),
               (Q(523,1000),Q(573,1000),Q(151,1000)))
    comparisons = 0
    optimization_budgets = 0
    for triple in triples:
        u,v,w = triple
        b,c = v+w,u+v
        factors = pair_factors(triple)
        l1,l2,lb = (factors[key] for key in ("L1","L2","Lb"))
        ensure(l1 > l2 > lb > 1, "eligibility gain ordering")
        p0,p1,p2,c0,c1 = b*b,b*(b+u),b*(b+2*u),b*c,b*c+u*v
        for a in range(max_pairs+1):
            for crossing in range(max_pairs+1):
                exact = {}
                for double in range(a+1):
                    for single in range(a-double+1):
                        for eligible_cross in range(crossing+1):
                            budget = 2*double+single+eligible_cross
                            value = p0**(a-double-single)*p1**single*p2**double*c0**(crossing-eligible_cross)*c1**eligible_cross
                            exact[budget] = max(exact.get(budget,Q(0)),value)
                            square_bound = factors["P"]**(2*a)*factors["E_squared"]**crossing*l1**max(0,2*budget-2*a-crossing)
                            ensure(value*value <= square_bound, "fractional eligibility bound")
                            ensure(value <= p0**a*c0**crossing*l1**budget, "crude eligibility bound")
                            comparisons += 1
                greedy = p0**a*c0**crossing
                ensure(exact[0] == greedy, "zero-budget optimization")
                optimization_budgets += 1
                for h,gain in enumerate([l1]*a+[l2]*a+[lb]*crossing,1):
                    greedy *= gain
                    ensure(exact[h] == greedy, "exact integral eligibility optimum")
                    optimization_budgets += 1
    return {"aggregate_allocations":comparisons, "optimal_budgets":optimization_budgets, "activity_triples":len(triples)}


def _bounded_set(value, name, upper):
    if not isinstance(value, (set, frozenset, tuple, list)) or len(value) > upper:
        raise ValueError(f"{name}: expected a bounded collection")
    for x in value:
        bounded_int(x, name, 1, upper)
    return frozenset(value)


def cyclic_graph(d, sums):
    bounded_int(d, "graph order", 1, MAX_STRUCTURE)
    sums = _bounded_set(sums, "sum positions", d)
    if not sums:
        raise ValueError("nonempty sum positions required")
    return {i:frozenset((h-i-1)%d+1 for h in sums) for i in range(1,d+1)}


def _independent(graph, chosen):
    return all(not (graph[v] & chosen) for v in chosen)


def container(d, sums, independent):
    graph = cyclic_graph(d,sums)
    independent = _bounded_set(independent,"independent set",d)
    if not _independent(graph,independent):
        raise ValueError("the supplied set is not independent, including loops")
    k = len(graph[1])
    t = isqrt(k)
    fingerprint = set()
    residual = set(graph)
    while residual:
        pivot = min(residual,key=lambda v:(-len(graph[v]&residual),v))
        if len(graph[pivot]&residual) <= t:
            break
        if pivot in independent:
            fingerprint.add(pivot)
            residual.difference_update(graph[pivot] | {pivot})
        else:
            residual.remove(pivot)
    return frozenset(fingerprint),frozenset(residual)


def reconstruct_container(d, sums, fingerprint):
    graph = cyclic_graph(d,sums)
    fingerprint = _bounded_set(fingerprint,"fingerprint",d)
    residual = set(graph)
    t = isqrt(len(graph[1]))
    while residual:
        pivot = min(residual,key=lambda v:(-len(graph[v]&residual),v))
        if len(graph[pivot]&residual) <= t:
            break
        if pivot in fingerprint:
            residual.difference_update(graph[pivot] | {pivot})
        else:
            residual.remove(pivot)
    return frozenset(residual)


def container_checks(max_order):
    bounded_int(max_order,"exhaustive graph order",1,MAX_GRAPH)
    graphs=instances=looped=0
    for d in range(1,max_order+1):
        all_sets = [frozenset(i+1 for i in range(d) if mask & (1<<i)) for mask in range(1<<d)]
        for sums in all_sets[1:]:
            graph = cyclic_graph(d,sums)
            graphs += 1
            looped += any(v in graph[v] for v in graph)
            k,t = len(sums),isqrt(len(sums))
            ensure(all(len(n)==k for n in graph.values()),"cyclic regularity")
            ensure(all(i in graph[j] for i in graph for j in graph[i]),"graph symmetry")
            fingerprints=set()
            for independent in all_sets:
                if not _independent(graph,independent):
                    continue
                f,r = container(d,sums,independent)
                fingerprints.add(f)
                ensure(independent <= f|r,"container containment")
                ensure(len(f)*(t+1)<=d,"fingerprint bound")
                ensure((2*k-t)*len(r)<=k*d,"loop-aware residual cut bound")
                delta=Q(t,2*(2*k-t))+Q(1,t+1)
                ensure(len(f|r)<=Q(d,2)+delta*d,"container size bound")
                ensure(reconstruct_container(d,sums,f)==r,"deterministic reconstruction")
                instances += 1
            ensure(len(fingerprints)<=sum(comb(d,j) for j in range(d//(t+1)+1)),"fingerprint-count bound")
    return {"graphs":graphs,"looped_graphs":looped,"independent_sets":instances}


def reflection_blocks(length):
    bounded_int(length,"structural length",1,MAX_STRUCTURE)
    blocks=tuple((i,length-i) for i in range(1,(length+1)//2))
    exceptions=frozenset({length} | ({length//2} if length%2==0 else set()))
    return blocks,exceptions


def standardize(word,k):
    if not stressed(word):
        raise ValueError("standardization requires an original stressed word")
    bounded_int(k,"standardization k",2,3)
    if word.count(3)<k*k:
        raise ValueError("word is outside the dense diagnostic class")
    length=len(word)
    width=(length+k-1)//k
    intervals=[tuple(i for i in range(start,min(start+width,length+1)) if word[i-1]==3)
               for start in range(1,length+1,width)]
    dense=[positions for positions in intervals if len(positions)>=k]
    ensure(dense,"dense interval pigeonhole")
    positions=dense[-1]
    d=max(positions)
    sums=frozenset(positions[:k])
    prefix=frozenset(range(max(1,d-width+1),d+1))
    tail=frozenset(i for i in range(d+1,length+1) if word[i-1]==3)
    overwrite=prefix|tail
    image=tuple(3 if i in prefix else 2 if i in tail else word[i-1] for i in range(1,length+1))
    return d,sums,overwrite,image


def translated_relations(length,d,eligible,overwrite,q):
    bounded_int(length,"structural length",1,MAX_STRUCTURE)
    bounded_int(d,"prefix endpoint",1,length)
    bounded_int(q,"original early mark",1,length//3)
    eligible=_bounded_set(eligible,"eligibility container",d)
    overwrite=_bounded_set(overwrite,"overwrite set",length)
    blocks,exceptions=reflection_blocks(length)
    index={coordinate:n for n,block in enumerate(blocks) for coordinate in block}
    relations=tuple((i,i+q) for i in sorted(eligible) if i+q<=d
                    and i not in overwrite and i+q not in overwrite
                    and i not in exceptions and i+q not in exceptions
                    and index[i]!=index[i+q])
    used=set()
    chosen=[]
    degrees=Counter()
    for i,j in relations:
        degrees[index[i]]+=1
        degrees[index[j]]+=1
        if index[i] not in used and index[j] not in used:
            chosen.append((i,j))
            used.update((index[i],index[j]))
    ensure(max(degrees.values(),default=0)<=4,"relation multigraph degree")
    ensure(8*len(chosen)>=len(relations),"greedy block matching size")
    ensure(len(relations)>=len(eligible)-q-2*len(overwrite)-5,"relation deletion bound")
    return relations,tuple(chosen)


def standardization_checks(max_length):
    bounded_int(max_length,"standardization length",1,MAX_LENGTH)
    standardized=marked=relations_count=selected_count=overwritten_marks=0
    for length in range(1,max_length+1):
        for word in stressed_words(length):
            for k in (2,3):
                if word.count(3)<k*k:
                    continue
                d,sums,overwrite,image=standardize(word,k)
                width=(length+k-1)//k
                ensure(all(d-width<h<=d for h in sums),"dense-window location")
                ensure(sum(word[i-1]==3 for i in range(d+1,length+1))<k*k,"tail three bound")
                ensure(len(overwrite)<=width+k*k,"overwrite bound")
                ensure(all(image[i-1]==word[i-1] for i in range(1,length+1) if i not in overwrite),"unchanged coordinates")
                ensure(all(x in (1,2) for x in image[d:]),"tail alphabet")
                blocks,exceptions=reflection_blocks(length)
                ensure(all((image[i-1],image[j-1])!=(1,1) for i,j in blocks),"global matching survives")
                ensure(all(image[i-1]!=1 for i in exceptions),"reflection exceptions")
                ones=frozenset(i for i in range(1,d+1) if image[i-1]==1)
                ensure(_independent(cyclic_graph(d,sums),ones),"image cyclic independence")
                f,r=container(d,sums,ones)
                eligible=f|r
                standardized+=1
                for q in range(1,length//3+1):
                    if word[q-1]!=1:
                        continue
                    retained,chosen=translated_relations(length,d,eligible,overwrite,q)
                    # The extraction uses only fixed parameters, never letters.
                    ensure((retained,chosen)==translated_relations(length,d,eligible,overwrite,q),"deterministic block matching")
                    ensure(all((image[i-1],image[j-1])!=(1,3) for i,j in retained),"original-mark translated prohibition")
                    marked+=1
                    relations_count+=len(retained)
                    selected_count+=len(chosen)
                    overwritten_marks+=q in overwrite
    # A large but non-enumerated structural example ensures a positive linear
    # matching count and tests the numerical 5L/12 threshold nonvacuously.
    length,d,q=240,239,40
    eligible=frozenset(range(1,d+1))
    overwrite=frozenset(range(236,240))
    retained,chosen=translated_relations(length,d,eligible,overwrite,q)
    lower=Q(length,12)-2*len(overwrite)-5
    ensure(lower>0 and len(retained)>=lower,"large-container relation bound")
    ensure(len(chosen)>0,"nonvacuous synthetic block matching")
    return {"dense_images":standardized,"original_early_marks":marked,
            "overwritten_early_marks":overwritten_marks,"retained_relations":relations_count,
            "selected_relations":selected_count,"synthetic_retained":len(retained),"synthetic_selected":len(chosen),
            "test_k":[2,3]}


def _block_assignments(left,right,x):
    return tuple(((a,b),x**(a+b)) for a,b in product(left,right) if (a,b)!=(1,1))


def forbidden_marginal_checks():
    alphabets=((1,2,3),(2,3),(1,2))
    checks=independence_checks=0
    for x in (Q(1,2),Q(33,50),Q(3,2)):
        whole=x+x*x+x**3
        eta=x**8/whole**4
        for source_partner,target_alphabet,target_partner in product(alphabets,alphabets[:2],alphabets):
            source=_block_assignments((1,2,3),source_partner,x)
            target=_block_assignments(target_alphabet,target_partner,x)
            source_total=sum(weight for _,weight in source)
            target_total=sum(weight for _,weight in target)
            source_one=sum(weight for letters,weight in source if letters[0]==1)
            target_three=sum(weight for letters,weight in target if letters[0]==3)
            ensure(source_total<=whole**2 and target_total<=whole**2,"block normalization bound")
            ensure(source_one/source_total>=x**3/whole**2,"source marginal")
            ensure(target_three/target_total>=x**5/whole**2,"target marginal")
            forbidden=sum(ws*wt for (s,ws),(t,wt) in product(source,target) if s[0]==1 and t[0]==3)
            ensure(forbidden==source_one*target_three,"independent two-block event")
            ensure(forbidden/(source_total*target_total)>=eta,"forbidden event lower bound")
            checks+=1
        # Two distinct relation-edges on four independent blocks, explicitly
        # summed rather than inferred from the event marginals above.
        source=_block_assignments((1,2,3),(1,2),x)
        target=_block_assignments((2,3),(1,2,3),x)
        z=sum(weight for _,weight in source)*sum(weight for _,weight in target)
        allowed=sum(a*b for (s,a),(t,b) in product(source,target) if not(s[0]==1 and t[0]==3))
        joint=sum(a*b*c*d for (s,a),(t,b),(u,c),(v,d) in product(source,target,source,target)
                  if not(s[0]==1 and t[0]==3) and not(u[0]==1 and v[0]==3))
        ensure(joint==allowed**2,"disjoint-edge product identity")
        ensure(joint/z**2<=(1-eta)**2,"two-event forbidden penalty")
        independence_checks+=1
    return {"local_marginals":checks,"four_block_product_checks":independence_checks}


def rational_certificate():
    x=Q(33,50)
    a=x*x+x**3
    original=a*(x+a)
    ensure(original-1==Q(1737269,15625000000)>0,"33/50 exceeds positive critical root")
    transformed=(a*a,a*a*(x+x*x),a*a*x**3)
    ensure(transformed==(Q(8169809769,15625000000),Q(22377108957291,39062500000000),Q(293598453668553,1953125000000000)),"transformed activities")
    upper=(Q(523,1000),Q(573,1000),Q(151,1000))
    ensure(all(u<v for u,v in zip(transformed,upper)),"coordinatewise rational domination")
    factors=pair_factors(upper)
    ensure(factors["P"]==Q(225707,250000),"rational P")
    ensure(factors["T"]==Q(927687,1000000),"rational T")
    ensure(factors["E_squared"]==Q(108835743993,121777343750),"rational E square")
    ensure(factors["P"]<Q(19,20) and factors["T"]<Q(19,20) and factors["E_squared"]<Q(19,20)**2,"strict 19/20 margins")
    endpoint=pair_factors((Q(2,3),Q(4,9),Q(8,27)))
    ensure(endpoint["E_squared"]==Q(1120000,1121931)<1,"critical E endpoint")
    ensure(endpoint["T"]==Q(64,81)<1,"critical T endpoint")
    # Derivative numerator for E(x)^2 = x^6(1+x)^4*(x^2+x+2)/(x^2+x+1).
    # The following symbolic integer identity certifies positivity for x>0.
    numerator=_mul(_shift(_power((1,1),4),6),(2,1,1))
    denominator=(1,1,1)
    derivative=lambda p:tuple(i*p[i] for i in range(1,len(p)))
    left=_add(_mul(derivative(numerator),denominator),tuple(-v for v in _mul(numerator,derivative(denominator))))
    right=_mul(_shift(_power((1,1),3),5),(12,37,51,50,26,10))
    ensure(left==right,"symbolic positive derivative certificate")
    return {"x":str(x),"P_original_minus_one":str(original-1),
            "transformed_activities":[str(v) for v in transformed],
            "dominating_activities":[str(v) for v in upper],
            "pair_factors":{k:str(factors[k]) for k in ("P","T","E_squared")},
            "margin":"P,T < 19/20; E_squared < (19/20)^2",
            "endpoint_E_squared":str(endpoint["E_squared"])}


def run_checks(max_length=12,boundary=10,graph_order=8,allocation=6,standardization_length=12):
    bounded_int(max_length,"maximum length",1,MAX_LENGTH)
    bounded_int(boundary,"boundary length",1,MAX_BOUNDARY)
    bounded_int(graph_order,"graph order",1,MAX_GRAPH)
    bounded_int(allocation,"allocation size",0,MAX_ALLOCATION)
    bounded_int(standardization_length,"standardization length",1,MAX_LENGTH)
    boundary_degrees=[]
    for r in range(1,boundary+1):
        p=boundary_polynomial(r)
        ensure(p==transformed_boundary_polynomial(r),f"boundary polynomial at r={r}")
        boundary_degrees.append(len(p)-1)
    length_rows=[]
    coefficient_total=(0,)
    for length in range(1,max_length+1):
        all_words=genus_polynomial(length)
        separated=genus_polynomial(length,True)
        ensure(separated==renewal_polynomial(length),f"length-refined renewal at L={length}")
        ensure(all(type(c) is int and c>=0 for c in all_words+separated), "nonnegative integral coefficients")
        ensure(all((all_words[g] if g<len(all_words) else 0) >= (separated[g] if g<len(separated) else 0)
                   for g in range(max(len(all_words),len(separated)))), "nonnegative early-one coefficients")
        coefficient_total=_add(coefficient_total,all_words)
        total,late=sum(all_words),sum(separated)
        length_rows.append({"length":length,"stressed":total,"separated":late,"early":total-late})
    ensure(coefficient_total[:3]==(0,0,0), "zero-genus conventions s_0=s_1=s_2=0")
    # Genus g forces L<=g-2 because the terminal letter is three.  Thus this
    # prefix is complete across all lengths, rather than a truncated-length sum.
    complete_genus=min(14,max_length+2)
    exact_coefficients=[coefficient_total[g] if g<len(coefficient_total) else 0 for g in range(complete_genus+1)]
    triples=((Q(1,2),Q(1,3),Q(1,5)),(Q(5,4),Q(2,3),Q(1,2)),
             (Q(523,1000),Q(573,1000),Q(151,1000)))
    general_count=0
    for activities in triples:
        u,v,w=activities
        mapped=activity_transform(activities)
        ensure((mapped[0]+mapped[1])/(mapped[1]+mapped[2])==(u+v)/(v+w),"activity ratio invariance")
        for r in range(1,boundary+1):
            ensure(general_boundary(r,activities)==u*(u+v)*activity_partition(r,mapped),"general activity transform")
            general_count+=1
    return {"report":274,"arithmetic":"integers and exact fractions only", "bounded_diagnostics_not_asymptotic_proofs":True,
            "parameters":{"max_length":max_length,"boundary":boundary,"graph_order":graph_order,"allocation":allocation,"standardization_length":standardization_length},
            "boundary_polynomial_degrees":boundary_degrees,"length_refined_counts":length_rows,
            "complete_genus_coefficients":exact_coefficients,"general_activity_identities":general_count,"eligibility":eligibility_checks(allocation),
            "containers":container_checks(graph_order),"standardization":standardization_checks(standardization_length),
            "forbidden_blocks":forbidden_marginal_checks(),"rational_certificate":rational_certificate()}


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    specs=(("max-length",12,1,MAX_LENGTH),("boundary",10,1,MAX_BOUNDARY),
           ("graph-order",8,1,MAX_GRAPH),("allocation",6,0,MAX_ALLOCATION),
           ("standardization-length",12,1,MAX_LENGTH))
    for name,default,low,high in specs:
        def convert(value,name=name,low=low,high=high):
            try:
                return parse_integer(value,name,low,high)
            except ValueError as exc:
                raise argparse.ArgumentTypeError(str(exc)) from exc
        parser.add_argument("--"+name,type=convert,default=default)
    args=parser.parse_args(argv)
    result=run_checks(args.max_length,args.boundary,args.graph_order,args.allocation,args.standardization_length)
    print(json.dumps(result,sort_keys=True,indent=2))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
