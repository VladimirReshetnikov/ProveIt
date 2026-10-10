#!/usr/bin/env python3
"""Division-free normal forms for finite weighted distributions.

The polynomial variables, in ascending prime order, are A_p. A normal
form is a sparse dict {(basis_grid_index, exponent_tuple): integer}.
Only Python's standard library is required. This is a generator, not the
independent certificate verifier. See the article for the all-level proof.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from math import prod
from typing import Mapping
import argparse
import json
from pathlib import Path

Term = tuple[int, tuple[int, ...]]
Vector = dict[Term, int]

def factor(n: int) -> dict[int, int]:
    if not isinstance(n, int) or n < 1:
        raise ValueError('level must be a positive integer')
    out: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out

@lru_cache(maxsize=None)
def layout(q: int) -> dict:
    if q < 2:
        raise ValueError('level must be at least 2')
    fac = factor(q)
    ps = tuple(fac)
    heights, bad, coordinates = [], [], []
    for a in range(q):
        cc = tuple((a*pow(q//p**fac[p], -1, p**fac[p])) % p**fac[p] for p in ps)
        hh = []
        for p, c in zip(ps, cc):
            if c == 0:
                hh.append(0)
            else:
                v = 0
                while c % p == 0:
                    c //= p
                    v += 1
                hh.append(fac[p]-v)
        bb = tuple(p for p, c in zip(ps, cc) if 1 <= c <= p**(fac[p]-1))
        coordinates.append(cc)
        heights.append(tuple(hh))
        bad.append(bb)
    basis = tuple(a for a in range(q) if not bad[a])
    order = tuple(sorted(range(q), key=lambda a: (sum(heights[a]), len(bad[a]), a)))
    return dict(q=q, primes=ps, exponents=tuple(fac.values()), basis=basis,
                order=order, heights=tuple(heights), bad=tuple(bad),
                coordinates=tuple(coordinates))

def add(v: Vector, w: Mapping[Term, int], scale: int = 1,
        variable: int | None = None) -> None:
    for (b, powers), c in w.items():
        if variable is not None:
            powers = tuple(e+(j == variable) for j, e in enumerate(powers))
        key = (b, powers)
        n = v.get(key, 0) + scale*c
        if n:
            v[key] = n
        elif key in v:
            del v[key]

def normal_forms(q: int) -> tuple[dict, dict[int, Vector]]:
    g = layout(q)
    ps = g['primes']
    pindex = {p: j for j, p in enumerate(ps)}
    zero = (0,)*len(ps)
    nf: dict[int, Vector] = {}
    positions = {a: j for j, a in enumerate(g['order'])}
    for a in g['order']:
        if not g['bad'][a]:
            nf[a] = {(a, zero): 1}
            continue
        p = g['bad'][a][0]
        parent = p*a % q
        other = [(a+j*(q//p)) % q for j in range(1, p)]
        assert positions[parent] < positions[a]
        assert all(positions[b] < positions[a] for b in other)
        out: Vector = {}
        add(out, nf[parent], variable=pindex[p])
        for b in other:
            add(out, nf[b], scale=-1)
        nf[a] = out
    return g, nf

def raw_rows(q: int):
    for p in factor(q):
        for k in range(q//p):
            yield p, p*k, tuple(k+j*(q//p) for j in range(p))

def check_all_rows(q: int, nf: Mapping[int, Vector]) -> int:
    ps = tuple(factor(q))
    count = 0
    for p, parent, lifts in raw_rows(q):
        out: Vector = {}
        for b in lifts:
            add(out, nf[b])
        add(out, nf[parent], scale=-1, variable=ps.index(p))
        if out:
            raise ArithmeticError(f'nonzero raw row at level {q}: {(p, parent)}')
        count += 1
    return count

def certificate(q: int) -> dict:
    g, nf = normal_forms(q)
    check_all_rows(q, nf)
    return {
        'schema': 'proveit.integral-distribution.normal-form.v1',
        'q': q, 'primes': list(g['primes']), 'basis': list(g['basis']),
        'ordered_nonbasis': [a for a in g['order'] if g['bad'][a]],
        'selected_rows': [{'pivot': a, 'prime': g['bad'][a][0],
                           'parent': g['bad'][a][0]*a % q}
                          for a in g['order'] if g['bad'][a]],
        'normal_forms': {str(a): [[b, list(ex), c] for (b, ex), c in sorted(nf[a].items())]
                         for a in range(q)},
        'scope': 'Exact polynomial identities modulo the declared raw prime rows; no numerical independence assertion.'
    }

def evaluate_nf(nf: Mapping[Term, int], values: tuple[int, ...]) -> dict[int, int]:
    out: dict[int, int] = {}
    for (b, powers), c in nf.items():
        c *= prod(v**e for v, e in zip(values, powers))
        out[b] = out.get(b, 0) + c
    return {b: c for b, c in out.items() if c}

def rank_f2(vectors) -> int:
    pivots: dict[int, int] = {}
    for v in vectors:
        while v:
            i = v.bit_length()-1
            if i in pivots:
                v ^= pivots[i]
            else:
                pivots[i] = v
                break
    return len(pivots)

def parity_case(q: int, bits: tuple[int, ...], check_rows: bool = True) -> dict:
    g = layout(q)
    if len(bits) != len(g['primes']) or any(b not in (0, 1) for b in bits):
        raise ValueError('one parity bit per prime is required')
    pix = {p: j for j, p in enumerate(g['primes'])}
    bix = {b: j for j, b in enumerate(g['basis'])}
    nf: dict[int, int] = {}
    for a in g['order']:
        if not g['bad'][a]:
            nf[a] = 1 << bix[a]
            continue
        p = g['bad'][a][0]
        v = nf[p*a % q] if bits[pix[p]] else 0
        for j in range(1, p):
            v ^= nf[(a+j*(q//p)) % q]
        nf[a] = v
    row_count = 0
    if check_rows:
        for p, parent, lifts in raw_rows(q):
            v = nf[parent] if bits[pix[p]] else 0
            for b in lifts:
                v ^= nf[b]
            if v:
                raise ArithmeticError('binary raw row failed')
            row_count += 1
    rank = rank_f2(nf[-b % q] ^ (1 << j) for j, b in enumerate(g['basis']))
    if q == 2:
        return dict(q=q, bits=list(bits), rank_J_minus_1=rank,
                    h_plus=0, h_minus=1, raw_rows_checked=row_count)
    h = len(g['basis'])//2-rank
    r = sum(p != 2 for p in g['primes']) + int(q % 4 == 0)
    prediction = (0 if any(p != 2 and bit == 0 for p, bit in zip(g['primes'], bits))
                  else 2**(r-1))
    if h != prediction:
        raise ArithmeticError(f'parity theorem failed: {(q, bits, h, prediction)}')
    return dict(q=q, bits=list(bits), rank_J_minus_1=rank,
                h_plus=h, h_minus=h, raw_rows_checked=row_count)

def polynomial_text(terms: Mapping[tuple[int, ...], int], ps: tuple[int, ...], latex=False) -> str:
    parts = []
    for powers, c in sorted(terms.items(), reverse=True):
        atoms = []
        for p, e in zip(ps, powers):
            if e:
                a = f'A_{{{p}}}' if latex else f'A{p}'
                if e != 1:
                    a += f'^{{{e}}}' if latex else f'**{e}'
                atoms.append(a)
        body = (' '.join(atoms) if latex else '*'.join(atoms))
        if abs(c) != 1 or not body:
            body = str(abs(c)) + ((' ' if latex else '*')+body if body else '')
        parts.append(('-' if c < 0 else '+', body))
    if not parts:
        return '0'
    out = ''.join(sign+body for sign, body in parts)
    return out[1:] if out[0] == '+' else out

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('q', type=int)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    data = certificate(args.q)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')
    print(f'Wrote level {args.q}, basis size {len(data["basis"])}, unit minor size {len(data["selected_rows"])}')


# Polynomial jets over F_2[u]/(u^length), stored in basis-major bit blocks.
def jet_multiply(v: int, f: int, length: int, dimension: int) -> int:
    out = 0
    blockmask = (1 << length)-1
    for b in range(dimension):
        block = (v >> (b*length)) & blockmask
        w, ff, h = 0, f, 0
        while ff:
            if ff & 1:
                w ^= block << h
            ff >>= 1
            h += 1
        out |= (w & blockmask) << (b*length)
    return out

def polynomial_product_f2(a: int, b: int, length: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out & ((1 << length)-1)

def jet_case(q: int, length: int, weights: tuple[int, ...]) -> dict:
    if length < 1:
        raise ValueError('positive jet length is required')
    g = layout(q)
    if len(weights) != len(g['primes']):
        raise ValueError('one encoded binary jet per prime is required')
    ps, B = g['primes'], g['basis']
    d = len(B)
    bi = {b: j for j, b in enumerate(B)}
    nf = {}
    def mul(v, a):
        return jet_multiply(v, a, length, d)
    for a in g['order']:
        if not g['bad'][a]:
            nf[a] = 1 << (bi[a]*length)
            continue
        p = g['bad'][a][0]
        v = mul(nf[p*a % q], weights[ps.index(p)])
        for j in range(1, p):
            v ^= nf[(a+j*q//p) % q]
        nf[a] = v
    for p, parent, lifts in raw_rows(q):
        v = mul(nf[parent], weights[ps.index(p)])
        for a in lifts:
            v ^= nf[a]
        assert v == 0
    rank = rank_f2(mul(nf[-b % q], 1 << k) ^ (1 << (j*length+k))
                   for j, b in enumerate(B) for k in range(length))
    scalars = []
    for p, a in zip(ps, weights):
        a &= (1 << length)-1
        if p != 2:
            scalars.append(a ^ 1)
        elif q % 4 == 0:
            scalars.append(polynomial_product_f2(a, a ^ 1, length))
    if q == 2:
        hp, hm, v = 0, length, None
    else:
        v = min((length if f == 0 else (f & -f).bit_length()-1) for f in scalars)
        hp = hm = length*d//2-rank
        assert hp == v*2**(len(scalars)-1), (q, length, weights, hp, v)
    return dict(q=q, length=length, weights_binary=list(weights),
                koszul_scalars_binary=scalars, valuation=v,
                rank_J_minus_1=rank, h_plus=hp, h_minus=hm,
                free_rank_plus=(length if q == 2 else length*d//2),
                free_rank_minus=(0 if q == 2 else length*d//2))

if __name__ == '__main__':
    main()
