"""Exact shuffle normal forms for single-argument multiple polylogarithms.

All calculations use integers or fractions. A verification re-expands every
normal form as words; no floating-point period recognition is involved.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd
from pathlib import Path
import argparse
import json

Word = tuple

@lru_cache(None)
def shuffle(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    result = Counter()
    for w, c in shuffle(u[1:], v).items():
        result[(u[0],) + w] += c
    for w, c in shuffle(u, v[1:]).items():
        result[(v[0],) + w] += c
    return dict(result)

def add(target, source, scale=Fraction(1)):
    for key, coefficient in source.items():
        target[key] = target.get(key, Fraction(0)) + scale * coefficient
        if target[key] == 0:
            del target[key]
    return target

def is_lyndon(w):
    return bool(w) and all(w < w[k:] + w[:k] for k in range(1, len(w)))

def lyndon_factorization(w):
    """Duval's nonincreasing Chen-Fox-Lyndon factorization."""
    answer = []
    i = 0
    while i < len(w):
        j, k = i + 1, i
        while j < len(w) and w[k] <= w[j]:
            k = i if w[k] < w[j] else k + 1
            j += 1
        while i <= k:
            answer.append(w[i:i+j-k])
            i += j - k
    return tuple(answer)

def expand_monomial(factors):
    result = {(): Fraction(1)}
    for factor in factors:
        new = {}
        for word, c in result.items():
            add(new, shuffle(word, factor), c)
        result = new
    return result

@lru_cache(None)
def normal_form(w):
    if not w:
        return {(): Fraction(1)}
    if is_lyndon(w):
        return {(w,): Fraction(1)}
    factors = lyndon_factorization(w)
    expansion = expand_monomial(factors)
    lead = expansion.pop(w)
    expected = 1
    for multiplicity in Counter(factors).values():
        expected *= factorial(multiplicity)
    if lead != expected or any(v >= w for v in expansion):
        raise ArithmeticError('Lyndon triangularity failed')
    result = {tuple(sorted(factors)): Fraction(1, lead)}
    for smaller, c in expansion.items():
        add(result, normal_form(smaller), -c/lead)
    return result

def expand_polynomial(polynomial):
    result = {}
    for factors, c in polynomial.items():
        add(result, expand_monomial(factors), c)
    return result

def indices(word):
    if not word or word[-1] != 1:
        raise ValueError('An admissible word must end in 1')
    result = []
    count = 0
    for letter in word:
        count += 1
        if letter == 1:
            result.append(count)
            count = 0
    return tuple(result)

def mobius(n):
    answer = 1
    prime = 2
    while prime * prime <= n:
        if n % prime == 0:
            n //= prime
            answer = -answer
            if n % prime == 0:
                return 0
            while n % prime == 0:
                n //= prime
        prime += 1
    return -answer if n > 1 else answer

def witt(weight, depth):
    value = sum(mobius(k)*comb(weight//k, depth//k)
                for k in range(1, gcd(weight, depth)+1)
                if weight % k == 0 and depth % k == 0)
    if value % weight:
        raise ArithmeticError('Witt formula was not integral')
    return value // weight

def words(weight, depth=None):
    for prefix in product((0, 1), repeat=weight-1):
        w = prefix + (1,)
        if depth is None or sum(w) == depth:
            yield w

def serialize(polynomial):
    return [{'coefficient':str(c),
             'factors':[list(indices(w)) for w in factors]}
            for factors,c in sorted(polynomial.items())]

def verify(max_weight):
    counts = []
    checked = 0
    for weight in range(1, max_weight+1):
        all_words = list(words(weight))
        for w in all_words:
            factors = lyndon_factorization(w)
            if tuple(x for factor in factors for x in factor) != w:
                raise AssertionError('Factorization does not concatenate')
            if any(f[-1] != 1 for f in factors):
                raise AssertionError('Factor left the ending-in-one subalgebra')
            if expand_polynomial(normal_form(w)) != {w: Fraction(1)}:
                raise AssertionError('Normal form did not replay')
            checked += 1
        for depth in range(1, weight+1):
            basis = [w for w in all_words if sum(w)==depth and is_lyndon(w)]
            predicted = witt(weight,depth)
            if len(basis) != predicted:
                raise AssertionError('Witt count did not match enumeration')
            counts.append({'weight':weight,'depth':depth,
                           'word_count':comb(weight-1,depth-1),
                           'product_rank':comb(weight-1,depth-1)-predicted,
                           'indecomposables':predicted,
                           'lyndon_indices':[list(indices(w)) for w in basis]})
    triples = {','.join(map(str,indices(w))):serialize(normal_form(w))
               for w in words(6,3)}
    doubles = {','.join(map(str,indices(w))):serialize(normal_form(w))
               for w in words(5,2)}
    # The weight-five target is certified by two specific product shuffles.
    li14 = shuffle((1,), (0,0,0,1))
    li23 = shuffle((0,1), (0,0,1))
    target = {}
    add(target,li14,960)
    add(target,li23,-224)
    want = {(0,0,0,1,1):Fraction(576),
            (0,0,1,0,1):Fraction(288),
            (0,1,0,0,1):Fraction(736),
            (1,0,0,0,1):Fraction(960)}
    if target != want:
        raise AssertionError('Weight-five certificate failed')
    return {'status':'PASS','arithmetic':'exact integers and fractions',
            'max_weight':max_weight,'normal_forms_reexpanded':checked,
            'bigraded_sectors_checked':len(counts),
            'counts':counts,'weight5_doubles':doubles,
            'weight6_triples':triples,
            'weight5_product_certificate':{
                '960_Li1_Li4_minus_224_Li2_Li3':
                {','.join(map(str,indices(w))):str(c) for w,c in target.items()}}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-weight', type=int, default=9)
    parser.add_argument('--output', type=Path, default=Path('shuffle_verification.json'))
    args = parser.parse_args()
    result = verify(args.max_weight)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in
                      ['status','max_weight','normal_forms_reexpanded',
                       'bigraded_sectors_checked']},indent=2))

if __name__ == '__main__':
    main()
