#!/usr/bin/env python3
"""Exact finite checks for arrangement degeneracy refinements (standard library).

These tests check finite instances and identities, not the general theorems.
Run from any directory; results are written to ../data/verification.json.
"""
from __future__ import annotations
import itertools as it
import json
import math
import platform
import random
import time
from fractions import Fraction
from pathlib import Path

SEED = 20261006

def central_trinomial(n: int) -> int:
    if n < 0:
        raise ValueError('n must be nonnegative')
    return sum(math.comb(n, j)*math.comb(n-j, j) for j in range(n//2+1))

def hyperplane_formula(d: int) -> int:
    if d < 1:
        raise ValueError('d must be positive')
    return (central_trinomial(2*d)-2*math.comb(2*d,d)+1)//2

def primitive(v: tuple[int, ...]) -> tuple[int, ...] | None:
    if not any(v):
        return None
    g = math.gcd(*v)
    s = 1 if next(x for x in v if x) > 0 else -1
    return tuple(s*x//g for x in v)

def mod_projective(v: tuple[int, ...], p: int) -> tuple[int, ...] | None:
    v = tuple(x % p for x in v)
    if not any(v):
        return None
    inv = pow(next(x for x in v if x), -1, p)
    return tuple(x*inv % p for x in v)

def hyperplane_normals(d: int, p: int | None = None) -> set[tuple[int, ...]]:
    w = (1,)*d+(-1,)*d
    out = set()
    for a in it.product((-1, 0, 1), repeat=2*d):
        balanced = sum(a) == 0 if p is None else sum(a) % p == 0
        if not balanced:
            continue
        # r_last = sum_{i<last} w_i r_i since w_last = -1.
        v = tuple(a[i]+a[-1]*w[i] for i in range(2*d-1))
        v = primitive(v) if p is None else mod_projective(v, p)
        if v is not None:
            out.add(v)
    return out

def rank_mod(rows: list[list[int]], p: int) -> int:
    if not rows:
        return 0
    a = [[x % p for x in r] for r in rows]
    m, n = len(a), len(a[0])
    r = 0
    for c in range(n):
        j = next((j for j in range(r,m) if a[j][c]), None)
        if j is None:
            continue
        a[r], a[j] = a[j], a[r]
        inv = pow(a[r][c],-1,p)
        a[r] = [v*inv % p for v in a[r]]
        for j in range(r+1,m):
            if a[j][c]:
                v = a[j][c]
                a[j] = [(x-v*y) % p for x,y in zip(a[j],a[r])]
        r += 1
        if r == m:
            break
    return r

def check_pivot_ranks() -> dict:
    rng = random.Random(SEED)
    trials = 0
    for k in range(1,7):
        for m in range(k):
            for _ in range(15):
                p, blocks = 11, 4
                c = [[rng.randrange(p) if s.bit_count() >= m else 0
                      for s in range(1<<k)] for _ in range(blocks)]
                s0 = (1<<m)-1
                c[0][s0] = rng.randrange(1,p)
                h = [rng.randrange(1,p) for _ in range(k)]
                rows = []
                for A in range(1<<k):
                    if A.bit_count() != m+1:
                        continue
                    row = []
                    for j in range(blocks):
                        for i in range(k):
                            S = A ^ (1<<i)
                            row.append(c[j][S]*math.prod(h[t] for t in range(k)
                                if (S>>t)&1) % p if (A>>i)&1 else 0)
                    rows.append(row)
                assert rank_mod(rows,p) >= k-m
                trials += 1
    return {'trials':trials, 'k_range':[1,6], 'field':11,
            'status':'all minimal-layer rank bounds passed'}

def cross_sections(p: int, d: int):
    w = (1,)*d+(-1,)*d
    for r in it.product(range(p),repeat=2*d-1):
        yield r+(sum(x*s for x,s in zip(r,w)) % p,)

def affine_pair_count(b: tuple[int,...], c: tuple[int,...],
                      r: tuple[int,...], p: int) -> int:
    """# y solving b.y=-sum(c), (b*r).y=-sum(c*r), by direct ranks."""
    u = [x % p for x in b]
    v = [x*y % p for x,y in zip(b,r)]
    rhs1 = -sum(c) % p
    rhs2 = -sum(x*y for x,y in zip(c,r)) % p
    rank = rank_mod([u,v],p)
    aug_rank = rank_mod([u+[rhs1],v+[rhs2]],p)
    return p**(len(b)-rank) if rank == aug_rank else 0

def check_all_small_witnesses(p: int) -> dict:
    """All ternary witnesses for k=1,d=2, counted by exact affine ranks."""
    d, blocks = 2, 4
    rs = list(cross_sections(p,d))
    inv2 = pow(2,-1,p)
    normals = hyperplane_normals(d,p)
    regular = {r for r in rs if all(sum(a*x for a,x in zip(v,r[:-1])) % p
                                   for v in normals)}
    tested = feasible = 0
    maximum = Fraction(0)
    maximum_regular_joint = Fraction(0)
    bound = Fraction(1,p*p)+Fraction(p-1,p**(2*d))
    denom = p**(4*d-1)
    for eta in it.product((-1,0,1),repeat=2*blocks):
        first = next((x for x in eta if x),0)
        if first != 1:  # quotient by eta -> -eta; zero is excluded
            continue
        b = tuple((eta[2*j]+eta[2*j+1])*inv2 % p for j in range(blocks))
        c = tuple((-eta[2*j]+eta[2*j+1])*inv2 % p for j in range(blocks))
        if not any(b): # block-parity witnesses
            continue
        tested += 1
        if sum(b) % p:
            continue
        feasible += 1
        count = reg_count = 0
        for r in rs:
            if sum(x*y for x,y in zip(b,r)) % p:
                continue
            n = affine_pair_count(b,c,r,p)
            count += n
            if r in regular:
                reg_count += n
        prob = Fraction(count,denom)
        reg_joint = Fraction(reg_count,denom)
        assert prob <= bound, (eta,prob,bound)
        assert reg_joint <= Fraction(1,p*p), (eta,reg_joint)
        maximum = max(maximum,prob)
        maximum_regular_joint = max(maximum_regular_joint,reg_joint)
    assert tested == (3**8-3**4)//2
    assert maximum == bound  # the explicitly exhibited witness attains it
    return {'p':p, 'k':1, 'd':2, 'sign_classes':tested,
            'classes_passing_constant_constraint':feasible,
            'maximum_probability':str(maximum),
            'sharp_bound':str(bound),
            'maximum_regular_joint_probability':str(maximum_regular_joint),
            'regular_cross_sections':len(regular), 'all_cross_sections':len(rs)}

def check_walsh_identity() -> dict:
    rng = random.Random(SEED+1)
    trials = 0
    for k in range(1,6):
        p = 17
        signs = list(it.product((-1,1),repeat=k))
        for _ in range(25):
            eta = [rng.choice((-1,0,1)) for e in signs]
            h = [rng.randrange(1,p) for _ in range(k)]
            x = [rng.randrange(p) for _ in range(k)]
            coeff = []
            for S in range(1<<k):
                coeff.append(sum(a*math.prod(e[i] for i in range(k) if (S>>i)&1)
                                 for a,e in zip(eta,signs))*pow(2**k,-1,p) % p)
            for A in range(1<<k):
                direct = sum(a*math.prod(x[i]+e[i]*h[i] for i in range(k)
                                         if (A>>i)&1) for a,e in zip(eta,signs)) % p
                expanded = 2**k * sum(coeff[S]*math.prod(h[i] for i in range(k)
                    if (S>>i)&1)*math.prod(x[i] for i in range(k)
                    if ((A^S)>>i)&1) for S in range(1<<k) if S&A == S) % p
                assert direct == expanded
                trials += 1
    return {'identity_instances':trials,'status':'all exact Walsh identities passed'}

def check_fixed_witness_sharpness() -> list[dict]:
    records = []
    for d,p in [(1,5),(2,5),(2,7),(3,7)]:
        w = (1,)*d+(-1,)*d
        # eta(e,j)=w_j: k=1 and the parity-with-one-coordinate-removed witness.
        total = sum(affine_pair_count(w,(0,)*(2*d),r,p)
                    for r in cross_sections(p,d))
        actual = Fraction(total,p**(4*d-1))
        expected = Fraction(1,p*p)+Fraction(p-1,p**(2*d))
        assert actual == expected
        records.append({'d':d,'p':p,'actual':str(actual),'expected':str(expected)})
    return records

def check_riesz_coefficients() -> dict:
    # Under a ternary kernel {0,+eta0,-eta0}, the constant term and the two
    # signed terms are the only contributions; all entries of eta0 are +/-1.
    out = []
    for n in (8,16,32,64):
        a = Fraction(1,2**n)
        b = a+2*Fraction(1,4**n)
        assert b == a*(1+Fraction(2,2**n))
        out.append({'vertices':n, 'bad_survival':str(a),
                    'good_survival':str(b),'ratio':str(b/a)})
    # These exact coefficients are not a simulation of the selection process.
    return {'status':'exact Fourier coefficient arithmetic checked','cases':out}

def main() -> None:
    start = time.monotonic()
    table = [{'d':d,'central_trinomial':central_trinomial(2*d),
              'H':hyperplane_formula(d)} for d in range(1,10)]
    enumeration = []
    for d in range(1,6):
        actual = len(hyperplane_normals(d))
        assert actual == hyperplane_formula(d)
        p = next(p for p in (5,7,11,13,17) if p>2*d)
        field_count = len(hyperplane_normals(d,p))
        assert field_count == actual
        enumeration.append({'d':d,'integer_classes':actual,'prime':p,
                            'finite_field_classes':field_count})
    small_characteristic = len(hyperplane_normals(3,5))
    assert small_characteristic == 57
    assert small_characteristic != hyperplane_formula(3)
    results = {'status':'PASS','seed':SEED,'python':platform.python_version(),
        'hyperplane_table':table,'hyperplane_enumeration':enumeration,
        'small_characteristic':{'d':3,'p':5,'actual_H':small_characteristic,
                                'large_characteristic_H':hyperplane_formula(3)},
        'walsh_identity':check_walsh_identity(),
        'minimal_layer_ranks':check_pivot_ranks(),
        'all_k1_d2_witnesses':[check_all_small_witnesses(5),check_all_small_witnesses(7)],
        'sharp_witness':check_fixed_witness_sharpness(),
        'riesz_coefficients':check_riesz_coefficients(),
        'limitations':['Finite checks are not a proof of the general statements.',
                       'No Lean file is compiled or supplied by this script.',
                       'No exhaustive full-arrangement census is claimed.']}
    results['elapsed_seconds'] = round(time.monotonic()-start,3)
    path = Path(__file__).resolve().parents[1]/'data'/'verification.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(results,indent=2))

if __name__ == '__main__':
    main()
