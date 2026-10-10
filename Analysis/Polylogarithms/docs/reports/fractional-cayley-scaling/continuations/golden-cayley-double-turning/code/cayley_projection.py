"""Exact constructive projection for the full convergent Cayley shuffle ideal.

Letters are outer first: Z=-1; 0,1,2,3 are i**j dt/(1-i**j*t).
The code is a research prototype; no numerical period evaluator is used.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
from math import comb, factorial

Z = -1
C = 0
B = 2


def add(out, p, factor=1):
    for w, c in p.items():
        value = out.get(w, 0) + factor*c
        if value:
            out[w] = value
        else:
            out.pop(w, None)
    return out


@lru_cache(None)
def shuffle(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    out = {}
    for w, c in shuffle(u[1:], v).items():
        out[(u[0],)+w] = out.get((u[0],)+w, 0)+c
    for w, c in shuffle(u, v[1:]).items():
        out[(v[0],)+w] = out.get((v[0],)+w, 0)+c
    return out


def multiply(p, q):
    out = {}
    for u, a in p.items():
        for v, b in q.items():
            add(out, shuffle(u, v), a*b)
    return out


def apply(operation, p):
    out = {}
    for w, c in p.items():
        add(out, operation(w), c)
    return out


def admissible(w):
    return not w or (w[0] != C and w[-1] != Z)


def conjugate(w):
    return tuple(x if x == Z else (-x)%4 for x in w)


def odd(p):
    out = {}
    for w, c in p.items():
        v = conjugate(w)
        if w < v:
            add(out, {w:c})
        elif w > v:
            add(out, {v:-c})
    return out


TAU = {Z:{C:1, B:-1}, C:{Z:1, B:1},
       1:{B:1, 3:-1}, B:{B:1}, 3:{B:1, 1:-1}}


@lru_cache(None)
def cayley(w):
    out = {():1}
    for letter in reversed(w):
        result = {}
        for prefix, c in out.items():
            for a, b in TAU[letter].items():
                result[prefix+(a,)] = c*b
        out = result
    return out


@lru_cache(None)
def concatenation_power(form_items, n):
    out = {():1}
    for _ in range(n):
        result = {}
        for prefix, c in out.items():
            for letter, coefficient in form_items:
                result[prefix+(letter,)] = c*coefficient
        out = result
    return out


@lru_cache(None)
def regularize(w):
    """C-equivariant endpoint projection z=-b/2, c=b/2.

    These substitutions are in shuffle-polynomial coordinates, not
    letter-by-letter substitutions inside concatenation words.
    """
    left = 0
    while left < len(w) and w[left] == C:
        left += 1
    right = 0
    while right < len(w) and w[len(w)-1-right] == Z:
        right += 1
    out = {}
    for r in range(left+1):
        first = concatenation_power(((B,Q(1,2)),(C,-1)),r)
        for s in range(right+1):
            last = concatenation_power(((B,Q(-1,2)),(Z,-1)),s)
            middle = {w[r:len(w)-s]:1}
            add(out, multiply(multiply(first,middle),last))
    assert all(admissible(v) for v in out)
    return out


@lru_cache(None)
def eulerian_permutations(n):
    """The first Eulerian idempotent, with inverse descents."""
    out = []
    for p in permutations(range(n)):
        inverse = [0]*n
        for j,k in enumerate(p):
            inverse[k] = j
        descents = sum(inverse[j] > inverse[j+1] for j in range(n-1))
        out.append((p,Q((-1)**descents,n*comb(n-1,descents))))
    return out


@lru_cache(None)
def eulerian(w):
    if not w:
        return {}
    out = {}
    for p,c in eulerian_permutations(len(w)):
        v = tuple(w[j] for j in p)
        add(out,{v:c})
    return out


@lru_cache(None)
def lifted_generator(w):
    return apply(regularize,eulerian(w))


@lru_cache(None)
def positive_generator(w):
    p = lifted_generator(w)
    out = {v:c/2 for v,c in p.items()}
    return add(out,apply(cayley,p),Q(1,2))


@lru_cache(None)
def convolution_power(w,k):
    if k == 0:
        return {():1} if not w else {}
    if len(w)<k:
        return {}
    out = {}
    for j in range(1,len(w)-k+2):
        a = positive_generator(w[:j])
        if a:
            add(out,multiply(a,convolution_power(w[j:],k-1)))
    return out


@lru_cache(None)
def projection(w):
    if not w:
        return {():1}
    out = {}
    for k in range(1,len(w)+1):
        add(out,convolution_power(w,k),Q(1,factorial(k)))
    assert all(admissible(v) for v in out)
    return out


def word(indices):
    out=[]
    previous=0
    for weight,color in indices:
        previous=(previous+color)%4
        out.extend([Z]*(weight-1)+[previous])
    return tuple(out)


def s6_target():
    """Imaginary part of a rational word expression exactly equal to
    485683200 times the frozen S6 residual; pi^7 is expressed via beta(7).
    """
    out = {}
    # S6 = Im (Li_6,1(i,1)+Li_6,1(i,-1)).
    add(out,{word(((6,1),(1,0))):1},485683200-665395200)
    add(out,{word(((6,1),(1,2))):1},485683200)
    add(out,{word(((4,1),(3,0))):1},-36864000)
    add(out,{word(((2,1),(5,0))):1},401080320)
    # beta(7)=61*pi^7/184320.
    add(out,{word(((7,1),)):1},Q(-258247*184320,61))
    add(out,shuffle(word(((2,1),)),word(((5,0),))),11750400)
    add(out,shuffle(word(((4,1),)),word(((3,0),))),109347840)
    add(out,shuffle(word(((6,1),)),word(((1,2),))),-971366400)
    return out


if __name__ == '__main__':
    import argparse,json,time
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-weight',type=int,default=3)
    parser.add_argument('--target',action='store_true')
    args=parser.parse_args()
    start=time.monotonic()
    counts={}
    for n in range(1,args.max_weight+1):
        total=0
        for w in product(range(-1,4),repeat=n):
            r=regularize(w)
            assert apply(cayley,r)==apply(regularize,cayley(w))
            p=projection(w)
            assert p==apply(projection,p)
            assert p==apply(projection,cayley(w))
            assert p==apply(projection,r)
            total+=1
        counts[n]=total
        print(json.dumps({'weight':n,'checked_words':total,
                          'elapsed_seconds':time.monotonic()-start}),flush=True)
    # Algebra multiplication, including nonadmissible inputs.
    pairs=0
    for n in range(2,args.max_weight+1):
        for k in range(1,n):
            for u in product(range(-1,4),repeat=k):
                for v in product(range(-1,4),repeat=n-k):
                    assert apply(projection,shuffle(u,v))==multiply(projection(u),projection(v))
                    pairs+=1
    print(json.dumps({'shuffle_pairs_checked':pairs,
                      'elapsed_seconds':time.monotonic()-start}),flush=True)
    if args.target:
        p=odd(apply(projection,s6_target()))
        print(json.dumps({'S6_projection_support':len(p),
                          'nonzero_witness':[(list(w),str(p[w])) for w in sorted(p)[:5]],
                          'elapsed_seconds':time.monotonic()-start}),flush=True)
