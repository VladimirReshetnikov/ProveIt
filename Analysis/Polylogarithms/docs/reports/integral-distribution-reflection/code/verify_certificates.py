#!/usr/bin/env python3
"""Independent exact verifier. Does not import the normal-form generator.

Reconstructs every raw row. Checks the advertised unit triangular minor;
then reduces e_a minus the delivered normal form directly by these rows,
using polynomial back-substitution. Also checks every raw row annihilates
the delivered normal-form matrix. No floating-point arithmetic is used.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from math import gcd, isqrt


if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')


def plus(out, key, c):
    v = out.get(key, 0)+c
    if v:
        out[key] = v
    elif key in out:
        del out[key]


def verify(path: Path) -> dict:
    d = json.loads(path.read_text(encoding='utf-8'))
    if d.get('schema') != 'proveit.integral-distribution.normal-form.v1':
        raise ValueError('unrecognized certificate schema')
    q, ps, B = d['q'], tuple(d['primes']), tuple(d['basis'])
    actual_primes = tuple(n for n in range(2, q+1)
                          if q % n == 0 and all(n % t for t in range(2, isqrt(n)+1)))
    assert ps == actual_primes
    z = (0,)*len(ps)
    nb = tuple(d['ordered_nonbasis'])
    assert len(set(B)) == len(B) and len(set(nb)) == len(nb)
    assert set(B).isdisjoint(nb) and set(B) | set(nb) == set(range(q))
    assert len(B) == sum(gcd(a, q) == 1 for a in range(q))
    nf = {}
    for a in range(q):
        terms = {}
        for b, ex, c in d['normal_forms'][str(a)]:
            ex = tuple(ex)
            assert b in B and len(ex) == len(ps) and all(isinstance(e, int) and e >= 0 for e in ex)
            assert isinstance(c, int) and c and (b, ex) not in terms
            terms[b, ex] = c
        nf[a] = terms
    for b in B:
        assert nf[b] == {(b, z): 1}

    def row(p, parent):
        assert p in ps and 0 <= parent < q and parent % p == 0
        r = {}
        k = parent//p
        for j in range(p):
            plus(r, (k+j*(q//p), z), 1)
        ex = tuple(int(t == p) for t in ps)
        plus(r, (parent, ex), -1)
        return r

    chosen = []
    seen = set()
    nbpos = {a: i for i, a in enumerate(nb)}
    assert len(d['selected_rows']) == len(nb)
    for i, rec in enumerate(d['selected_rows']):
        a, p, parent = rec['pivot'], rec['prime'], rec['parent']
        assert a == nb[i] and parent == p*a % q and (p, parent) not in seen
        seen.add((p, parent))
        r = row(p, parent)
        assert {(ex, c) for (b, ex), c in r.items() if b == a} == {(z, 1)}
        assert all(b in B or nbpos[b] < i for (b, ex) in r if b != a)
        chosen.append(r)

    # Back-substitution is independent of the generator's recursive normal form.
    for a in range(q):
        v = {(a, z): 1}
        for key, c in nf[a].items():
            plus(v, key, -c)
        for pivot, r in reversed(list(zip(nb, chosen))):
            multipliers = [(ex, c) for (b, ex), c in list(v.items()) if b == pivot]
            for ex, c in multipliers:
                for (b, ey), m in r.items():
                    plus(v, (b, tuple(x+y for x, y in zip(ex, ey))), -c*m)
        assert not v, ('normal-form certificate failed', a, v)

    count = 0
    for p in ps:
        for parent in range(0, q, p):
            v = {}
            for (a, ex), c in row(p, parent).items():
                for (b, ey), m in nf[a].items():
                    plus(v, (b, tuple(x+y for x, y in zip(ex, ey))), c*m)
            assert not v, ('raw-row residual', p, parent)
            count += 1
    return dict(file=path.name, q=q, rank=q-len(B), basis_size=len(B),
                minor_determinant=1, identities_verified=q, raw_rows_verified=count,
                exact=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('paths', type=Path, nargs='+')
    args = ap.parse_args()
    for path in args.paths:
        print(json.dumps(verify(path), sort_keys=True))
