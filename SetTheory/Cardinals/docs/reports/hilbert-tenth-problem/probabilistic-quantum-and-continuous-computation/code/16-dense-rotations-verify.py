#!/usr/bin/env python3
"""Exact-arithmetic checks for Dense Rotations, Undecidable Exactness.

Python 3.10+, standard library only. This verifies finite instances and local
algebra, not Higman's theorem, undecidability, density, or the entire manuscript.
Run: python verify.py --output verification_results.json
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm
from pathlib import Path
import json
import random
from typing import Iterable, Sequence

Quat = tuple[F, F, F, F]
Mat = tuple[tuple[F, ...], ...]
ONE: Quat = (F(1), F(0), F(0), F(0))
RAW = {1: (3, 4, 0, 0), -1: (3, -4, 0, 0),
       2: (3, 0, 4, 0), -2: (3, 0, -4, 0)}
LETTERS = (1, -1, 2, -2)
GEN: dict[int, Quat] = {s: tuple(F(v, 5) for v in q) for s, q in RAW.items()}


def mul(p: Sequence, q: Sequence) -> tuple:
    a, b, c, d = p
    e, f, g, h = q
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def conj(p: Sequence) -> tuple:
    return (p[0], -p[1], -p[2], -p[3])


def norm2(p: Sequence):
    return sum(x*x for x in p)


def reduce_word(w: Iterable[int]) -> tuple[int, ...]:
    out: list[int] = []
    for s in w:
        if not isinstance(s, int) or s == 0:
            raise ValueError('Letters must be nonzero signed integers.')
        if out and out[-1] == -s:
            out.pop()
        else:
            out.append(s)
    return tuple(out)


def inverse_word(w: Sequence[int]) -> tuple[int, ...]:
    return tuple(-x for x in reversed(w))


def eval_word(w: Iterable[int]) -> Quat:
    p = ONE
    for s in w:
        if s not in GEN:
            raise ValueError('F2 letters are 1,-1,2,-2.')
        p = mul(p, GEN[s])
    return p


def reduced_words(max_length: int):
    yield ()
    layer = [()]
    for _ in range(max_length):
        layer = [w+(s,) for w in layer for s in LETTERS
                 if not w or w[-1] != -s]
        yield from layer


def fraction_data(q: Sequence[F]) -> tuple[int, tuple[int, ...]]:
    den = lcm(*(x.denominator for x in q))
    return den, tuple(int(x*den) for x in q)


def exponent5(d: int) -> int | None:
    if d < 1:
        return None
    n = 0
    while d % 5 == 0:
        n += 1
        d //= 5
    return n if d == 1 else None


def split_mod5(q: Sequence[int]) -> tuple[tuple[int, int], ...]:
    a, b, c, d = q
    return (((a+2*b) % 5, (c+2*d) % 5),
            ((4*c+2*d) % 5, (a+3*b) % 5))


def projective(v: Sequence[int]) -> tuple[int, int]:
    x, y = (v[0] % 5, v[1] % 5)
    if x:
        z = pow(x, -1, 5)
        return (1, y*z % 5)
    if y:
        return (0, 1)
    raise ValueError('Zero vector has no projective class.')


IMAGE_LINES = {projective(v): s for s, v in
               {1: (1, 0), -1: (0, 1), 2: (3, 1), -2: (3, 4)}.items()}


def decode(q: Sequence[F]) -> tuple[int, ...] | None:
    """Decide membership in <(3+4i)/5,(3+4j)/5>, recovering the word."""
    q = tuple(F(x) for x in q)
    if len(q) != 4 or norm2(q) != 1:
        return None
    den, v = fraction_data(q)
    n = exponent5(den)
    if n is None:
        return None
    out = []
    for _ in range(n):
        m = split_mod5(v)
        column = next(((m[0][c], m[1][c]) for c in (0, 1)
                       if m[0][c] or m[1][c]), None)
        if column is None:
            return None
        s = IMAGE_LINES.get(projective(column))
        if s is None:
            return None
        z = mul(RAW[-s], v)
        if any(x % 25 for x in z):
            return None
        v = tuple(x//25 for x in z)
        out.append(s)
    return tuple(out) if v == (1, 0, 0, 0) else None


def expand(w: Iterable[int]) -> tuple[int, ...]:
    """Embed F_d into F_2 by x_j -> a^j b a^-j, with j>=1."""
    ans: list[int] = []
    for s in w:
        j = abs(s)
        if j == 0:
            raise ValueError('Generator indices must be positive.')
        ans.extend((1,)*j + ((2,) if s > 0 else (-2,)) + (-1,)*j)
    return reduce_word(ans)


def rho(w: Iterable[int]) -> Quat:
    return eval_word(expand(w))


def eye() -> Mat:
    return tuple(tuple(F(i == j) for j in range(4)) for i in range(4))


def mmul(a: Mat, b: Mat) -> Mat:
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(4))
                       for j in range(4)) for i in range(4))


def transpose(a: Mat) -> Mat:
    return tuple(zip(*a))


def phi(p: Quat, q: Quat) -> Mat:
    cols = [mul(mul(p, tuple(F(i == j) for i in range(4))), conj(q))
            for j in range(4)]
    return tuple(tuple(cols[j][i] for j in range(4)) for i in range(4))


def determinant(a: Mat) -> F:
    b = [list(row) for row in a]
    det = F(1)
    for k in range(4):
        p = next((i for i in range(k, 4) if b[i][k]), None)
        if p is None:
            return F(0)
        if p != k:
            b[p], b[k] = b[k], b[p]
            det = -det
        pivot = b[k][k]
        det *= pivot
        for i in range(k+1, 4):
            factor = b[i][k]/pivot
            for j in range(k+1, 4):
                b[i][j] -= factor*b[k][j]
    return det


def gates(rank: int, relators: Sequence[Sequence[int]]) -> list[Mat]:
    if rank < 2 or any(abs(s) > rank or s == 0 for w in relators for s in w):
        raise ValueError('Invalid presentation.')
    positive = [phi(rho((j,)), rho((j,))) for j in range(1, rank+1)]
    positive += [phi(rho(w), ONE) for w in relators]
    return [eye()] + positive + [transpose(m) for m in positive]


def mat_den(m: Mat) -> int:
    return lcm(*(x.denominator for row in m for x in row))


def mat_target(m: Mat) -> tuple[int, list[list[int]]]:
    q = mat_den(m)
    return q, [[int(x*q) for x in row] for row in m]


def make_trace(ss: Sequence[Mat], word: Sequence[int], D: int):
    d = [1]
    ys = [[[int(i == k)+1 for k in range(4)] for i in range(4)]]
    es = []
    current = eye()
    for label in word:
        if not 0 <= label < len(ss):
            raise ValueError('Invalid gate label.')
        es.append([int(j == label) for j in range(len(ss))])
        current = mmul(current, ss[label])
        d.append(d[-1]*D)
        ys.append([[int(current[i][k]*d[-1])+d[-1] for k in range(4)]
                   for i in range(4)])
    q, target = mat_target(current)
    return es, d, ys, q, target


def residuals(bs: Sequence[Sequence[Sequence[int]]], D: int,
              es: Sequence[Sequence[int]], ds: Sequence[int],
              ys: Sequence[Sequence[Sequence[int]]], q: int,
              target: Sequence[Sequence[int]]) -> list[int]:
    """The manuscript's quadratic equations; P_n is their squared sum."""
    n = len(es)
    if q < 1 or len(ds) != n+1 or len(ys) != n+1:
        raise ValueError('Malformed certificate parameters.')
    if ds[0] != 1 or ys[0] != [[int(i == k)+1 for k in range(4)] for i in range(4)]:
        raise ValueError('Initial data are fixed constants, not witnesses.')
    rr: list[int] = []
    for t in range(n):
        rr.extend(e*(e-1) for e in es[t])
        rr.append(sum(es[t])-1)
        rr.append(ds[t+1]-D*ds[t])
        for i in range(4):
            for k in range(4):
                value = sum(es[t][j]*sum((ys[t][i][h]-ds[t])*bs[j][h][k]
                                         for h in range(4)) for j in range(len(bs)))
                rr.append(ys[t+1][i][k]-ds[t+1]-value)
    rr.extend(q*(ys[n][i][k]-ds[n])-ds[n]*target[i][k]
              for i in range(4) for k in range(4))
    return rr


def encoded_matrix(m: Mat) -> dict:
    q, nums = mat_target(m)
    return {'denominator': q, 'numerator_matrix': nums}


def main(output: Path) -> None:
    results: dict = {'arithmetic': 'Python fractions.Fraction and integers; no floating point',
                    'scope': 'Finite tests, not a formal proof or universal gate instantiation'}
    u = {1: (1, 0), -1: (0, 1), 2: (3, 1), -2: (3, 4)}
    v = {1: (1, 0), -1: (0, 1), 2: (1, 3), -2: (1, 2)}
    table = []
    for s in LETTERS:
        assert split_mod5(RAW[s]) == tuple(tuple(u[s][i]*v[s][j] % 5 for j in range(2)) for i in range(2))
        row = []
        for t in LETTERS:
            value = sum(v[s][i]*u[t][i] for i in range(2)) % 5
            assert (value == 0) == (t == -s)
            row.append(value)
        table.append(row)
    results['mod5_pairing_table_order_1_minus1_2_minus2'] = table
    count = 0
    for w in reduced_words(8):
        p = (1, 0, 0, 0)
        for s in w:
            p = mul(p, RAW[s])
        assert norm2(p) == 25**len(w)
        assert not w or any(x % 5 for x in p)
        q = tuple(F(x, 5**len(w)) for x in p)
        assert fraction_data(q)[0] == 5**len(w)
        assert decode(q) == w
        count += 1
    results['reduced_words_checked_including_empty'] = count
    results['maximum_reduced_word_length'] = 8
    nonmembers = [(-1, 0, 0, 0), (0, 1, 0, 0),
                  (F(1, 2), F(1, 2), F(1, 2), F(1, 2)),
                  (F(5, 13), F(12, 13), 0, 0)]
    assert all(decode(tuple(F(x) for x in q)) is None for q in nonmembers)
    results['decoder_negative_examples'] = len(nonmembers)
    rng = random.Random(20260930)
    for _ in range(100):
        p, q, r, s = [eval_word(rng.choices(LETTERS, k=6)) for _ in range(4)]
        assert phi(mul(p, r), mul(q, s)) == mmul(phi(p, q), phi(r, s))
        assert mmul(phi(p, q), transpose(phi(p, q))) == eye()
        assert determinant(phi(p, q)) == 1
    results['spin4_random_homomorphism_orthogonality_determinant_tests'] = 100
    # G = <x,y,t | [x,y]> = Z^2 * Z: explicitly NOT the universal presentation.
    relator = (1, 2, -1, -2)
    ss = gates(3, [relator])
    D = lcm(*(mat_den(m) for m in ss))
    assert exponent5(D) is not None
    bs = [[[int(x*D) for x in row] for row in m] for m in ss]
    for m in ss:
        assert mmul(m, transpose(m)) == eye() and determinant(m) == 1
    good, mutated = 0, 0
    for n in range(4):
        for word in product(range(len(ss)), repeat=n):
            es, ds, ys, q, target = make_trace(ss, word, D)
            rr = residuals(bs, D, es, ds, ys, q, target)
            assert len(rr) == n*(len(ss)+18)+16
            assert all(x == 0 for x in rr)
            assert all(x >= 0 for y in ys for row in y for x in row)
            assert all(x <= 2*ds[t] for t, y in enumerate(ys) for row in y for x in row)
            good += 1
            target[0][0] += 1
            assert sum(x*x for x in residuals(bs, D, es, ds, ys, q, target)) > 0
            target[0][0] -= 1
            mutated += 1
            if n:
                ys[n][0][0] += 1
                assert sum(x*x for x in residuals(bs, D, es, ds, ys, q, target)) > 0
                ys[n][0][0] -= 1
                ds[n] += 1
                assert sum(x*x for x in residuals(bs, D, es, ds, ys, q, target)) > 0
                ds[n] -= 1
                es[0][word[0]] = 2
                assert sum(x*x for x in residuals(bs, D, es, ds, ys, q, target)) > 0
                es[0][word[0]] = 1
                mutated += 3
    results['example_presentation'] = '<x,y,t | x y x^-1 y^-1> = Z^2 * Z (decidable, not universal)'
    results['example_number_of_labeled_gates_including_identity'] = len(ss)
    results['example_common_denominator'] = D
    results['example_denominator_exponent'] = exponent5(D)
    results['bounded_trace_valid_tests_horizon_0_to_3'] = good
    results['bounded_trace_mutations_rejected'] = mutated
    # Uniform local-hardness commutator bound, checked on a concrete rotation.
    eps = F(1, 5)
    t = rho((3,))
    tk = ONE
    k = 0
    while True:
        k += 1
        tk = mul(tk, t)
        if norm2(tuple(tk[i]-ONE[i] for i in range(4))) < (eps/4)**2:
            break
        if k > 10000:
            raise RuntimeError('Small-angle search did not finish in the test budget.')
    p = rho((1,))
    c = mul(mul(mul(p, tk), conj(p)), conj(tk))
    cm = phi(c, ONE)
    frob2 = sum((cm[i][j]-F(i == j))**2 for i in range(4) for j in range(4))
    assert frob2 < eps**2
    results['locality_example_epsilon'] = str(eps)
    results['locality_power_k'] = k
    results['locality_squared_frobenius_error'] = str(frob2)
    output.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
    example = {'notice': 'A concrete decidable illustration, not a universal gate list.',
               'presentation': results['example_presentation'],
               'gate_label_order': ['I', 'diag(x)', 'diag(y)', 'diag(t)', 'left([x,y])',
                                    'diag(x)^-1', 'diag(y)^-1', 'diag(t)^-1', 'left([x,y])^-1'],
               'common_denominator': D, 'gates': [encoded_matrix(m) for m in ss],
               'relator_quaternion': [str(x) for x in rho(relator)],
               'relator_expanded_reduced_length': len(expand(relator)),
               'horizon_2_witness_variables': 2*(len(ss)+17),
               'horizon_2_squared_equations': 2*(len(ss)+18)+16}
    output.with_name('example_gates.json').write_text(json.dumps(example, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    main(args.output)
