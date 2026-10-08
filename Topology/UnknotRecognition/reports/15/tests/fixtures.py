"""Deterministic exact complexes and sharpness witnesses. SPDX-License-Identifier: MIT-0"""
import random
from radical import *


def nested_matching(k, j):
    return tuple(sorted([(0, 2*j+1)] + [(2*t-1, 2*t) for t in range(1, j+1)]
                        + [(t, t+1) for t in range(2*j+2, 2*k, 2)]))


def sharp_word(alg, k):
    if k < 1:
        raise ValueError('positive k required')
    ids = [alg.intern(nested_matching(k, j)) for j in range(k)]
    path = ids + ids[-2::-1] if k > 1 else ids
    factors = [1]*(len(path)-1)
    path.append(ids[0])
    factors.append(2)  # dot on circle zero of End(a_0)
    return path, factors


def word_product(alg, path, factors):
    result = 1
    for i, f in enumerate(factors):
        result = alg.compose(path[0], path[i], path[i+1], result, f)
    return result


def sharp_transfer_complex(alg, k):
    path, factors = sharp_word(alg, k)
    q = len(factors)
    objects = [Obj(path[0], 0)]
    for mid in path[1:-1]:
        objects.extend([Obj(mid, 0), Obj(mid, 1)])
    objects.append(Obj(path[-1], 1))
    d = zero(objects, objects)
    for r in range(1, q):
        d.cols[2*r-1][2*r] = 1
    for r, f in enumerate(factors):
        source = 0 if r == 0 else 2*r-1
        target = 2*r+2 if r < q-1 else len(objects)-1
        d.cols[source][target] = f
    return d


def gauge_complex(alg, k, seed, pairs=4, survivors=4, moves=24):
    rng = random.Random(seed)
    ids = [alg.intern(x) for x in matchings(tuple(range(2*k)))]
    objects = []
    for _ in range(pairs):
        a, h = rng.choice(ids), rng.randrange(2)
        objects.extend([Obj(a, h), Obj(a, h+1)])
    objects.extend(Obj(rng.choice(ids), rng.randrange(3)) for _ in range(survivors))
    d = zero(objects, objects)
    for p in range(pairs):
        d.cols[2*p][2*p+1] = 1
    # A minimal two-term residual block; no edge leaves its degree-one targets.
    for j in range(2*pairs, len(objects)):
        if objects[j].degree == 0:
            for i in range(2*pairs, len(objects)):
                if objects[i].degree == 1:
                    c = alg.basis(objects[j].matching, objects[i].matching)[1]
                    f = rng.getrandbits(1 << c)
                    if objects[j].matching == objects[i].matching:
                        f &= ~1
                    if f:
                        d.cols[j][i] = f
    for _ in range(moves):
        h = rng.randrange(3)
        same_degree = [i for i,o in enumerate(objects) if o.degree == h]
        if len(same_degree) < 2:
            continue
        a,b = rng.sample(same_degree,2)
        c = alg.basis(objects[a].matching, objects[b].matching)[1]
        f = rng.getrandbits(1 << c)
        if not f:
            continue
        u = identity(objects)
        u.cols[a][b] = f
        d = mul(u, mul(d,u,alg),alg)  # off-diagonal elementary map squares to identity
    return d
