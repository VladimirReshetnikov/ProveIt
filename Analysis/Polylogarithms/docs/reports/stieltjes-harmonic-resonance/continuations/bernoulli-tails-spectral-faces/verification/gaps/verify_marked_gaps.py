#!/usr/bin/env python3
"""Independent finite algebra and numerical checks for local marked gaps.

This is diagnostic evidence; the all-parameter analytic proof is in notes.md.
Only Python's standard library and mpmath are used.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path
import json
import time

import mpmath as mp


def add_exponents(a, b):
    return tuple(sorted(a + b))


def canonical_word(word):
    return tuple((tuple(sorted(e)), tuple(sorted(tails))) for e, tails in word)


@lru_cache(maxsize=None)
def compile_tails(word):
    """H of decorated letters -> bare H and endpoint Q factors.

    A letter is (exponent-label tuple, tuple of unshifted Q parameters).
    The identity used is the proved one-tail insertion/deconcatenation law.
    """
    selected = next((i for i, (_, tails) in enumerate(word) if tails), None)
    if selected is None:
        return Counter({(tuple(e for e, _ in word), ()): 1})
    i = selected
    e, tails = word[i]
    u = tails[0]
    reduced = list(word)
    reduced[i] = (e, tails[1:])
    reduced = canonical_word(reduced)
    out = Counter()
    for (bare, boundary), coefficient in compile_tails(reduced).items():
        out[(bare, tuple(sorted(boundary + (u,))))] += coefficient
    for slot in range(i + 1):
        inserted = reduced[:slot] + ((u, ()),) + reduced[slot:]
        out.update(compile_tails(canonical_word(inserted)))
    for slot in range(i + 1):
        merged = list(reduced)
        olde, oldtails = merged[slot]
        merged[slot] = (add_exponents(olde, u), oldtails)
        out.update(compile_tails(canonical_word(merged)))
    return out


def gap_product(blocks):
    """Compile product of gaps Q_U(z+1)-Q_U(y).

    Every factor has 3 unshifted choices because Q_U(z+1)=Q_U(z)-z^-U.
    Endpoints s,t have labels -2,-1; marked parameters use positive labels.
    """
    out = Counter()
    for choices in product(range(3), repeat=len(blocks)):
        upper_e, lower_e = (-2,), (-1,)
        upper_q, lower_q = [], []
        coefficient = 1
        for u, choice in zip(blocks, choices):
            if choice == 0:
                lower_q.append(u)
            elif choice == 1:
                lower_e = add_exponents(lower_e, u)
                coefficient *= -1
            else:
                upper_q.append(u)
                coefficient *= -1
        word = canonical_word(((upper_e, tuple(upper_q)),
                               (lower_e, tuple(lower_q))))
        for key, value in compile_tails(word).items():
            out[key] += coefficient * value
    return Counter({k: v for k, v in out.items() if v})


def partitions(items):
    """Set partitions with canonical block order, no repetitions."""
    items = tuple(items)
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for p in partitions(rest):
        yield ((first,),) + p
        for i in range(len(p)):
            yield p[:i] + (tuple(sorted((first,) + p[i])),) + p[i + 1:]


def check_symbolic(k):
    lhs = Counter()
    for permutation in permutations(range(1, k + 1)):
        lhs[(((-2,),) + tuple((i,) for i in permutation) + ((-1,),), ())] += 1
    rhs = Counter()
    number_partitions = 0
    for partition in partitions(range(1, k + 1)):
        number_partitions += 1
        mu = (-1) ** (k - len(partition))
        for block in partition:
            mu *= factorial(len(block) - 1)
        for key, value in gap_product(partition).items():
            rhs[key] += mu * value
    residual = Counter({key: rhs[key] - lhs[key] for key in rhs.keys() | lhs.keys()
                        if rhs[key] != lhs[key]})
    assert not residual, (k, residual)
    return {"marked_count": k, "set_partitions": number_partitions,
            "permutations": factorial(k), "exact_residual_terms": 0}


def z_truncated(arrays, n):
    dp = [mp.mpf(1)] * (n + 1)
    for values in reversed(arrays):
        new = [mp.mpf(0)] * (n + 1)
        running = mp.mpf(0)
        for j in range(n):
            running += values[j] * dp[j]
            new[j + 1] = running
        dp = new
    return dp[n]


class GenericCheck:
    def __init__(self, a, b, n):
        self.a, self.b, self.n = a, b, n
        self.array_cache = {}
        self.z_cache = {}
        self.h_cache = {(): mp.mpf(1)}

    def values(self, c, letter):
        key = c, letter
        if key not in self.array_cache:
            s, tails = letter
            arr = []
            for j in range(self.n):
                x = c + j
                value = x ** (-s)
                for u, shift in tails:
                    value *= mp.zeta(u, x + shift)
                arr.append(value)
            self.array_cache[key] = arr
        return self.array_cache[key]

    def z(self, c, word):
        key = c, word
        if key not in self.z_cache:
            self.z_cache[key] = z_truncated([self.values(c, l) for l in word], self.n)
        return self.z_cache[key]

    def h(self, word):
        if word not in self.h_cache:
            value = self.z(self.b, word)
            for cut in range(1, len(word) + 1):
                value -= self.z(self.a, word[:cut]) * self.h(word[cut:])
            self.h_cache[word] = value
        return self.h_cache[word]

    def e_gap(self, s, t, blocks):
        value = mp.mpf(0)
        for choices in product((0, 1), repeat=len(blocks)):
            upper, lower = [], []
            sign = 1
            for u, choice in zip(blocks, choices):
                if choice == 0:
                    lower.append((u, 1))
                else:
                    upper.append((u, 0))
                    sign *= -1
            value += sign * self.h(((s, tuple(upper)), (t, tuple(lower))))
        return value


def check_noninteger_generic(n):
    a = mp.mpc('2.6', '0.17')
    b = mp.mpc('1.3', '-0.11')
    s, t, u, v = map(mp.mpf, ('13.1', '12.4', '12.7', '13.3'))
    checker = GenericCheck(a, b, n)
    bare = lambda *w: tuple((p, ()) for p in w)
    lhs = checker.h(bare(s, u, v, t)) + checker.h(bare(s, v, u, t))
    rhs = checker.e_gap(s, t, (u, v)) - checker.e_gap(s, t, (u + v,))
    return {"n": n, "absolute_residual": mp.nstr(abs(lhs - rhs), 12),
            "lhs": mp.nstr(lhs, 45), "rhs": mp.nstr(rhs, 45)}


def check_noninteger_log_pair(n):
    """Actual u=v=0 derivative via independently grouped ordinary sums.

    The top-pair tails are symmetrized BEFORE continuation: the ordinary
    stuffle formula evaluates their sum, whose germ is regular at (0,0).
    Individual singular double zeta terms are never differentiated.
    """
    a = mp.mpc('2.6', '0.17')
    b = mp.mpc('1.3', '-0.11')
    s, t = mp.mpf('13.1'), mp.mpf('12.4')
    arrays = {}
    zeta0prime = {}
    zeta0second = {}
    for c in (a, b):
        lg = mp.loggamma(c)
        rz = mp.diff(lambda v: mp.zeta(v, c), 0, 2)
        zeta0prime[c] = lg - mp.log(2 * mp.pi) / 2
        zeta0second[c] = rz
        dat = {key: [] for key in ('fs', 'ft', 'mark', 'lg', 'lgp', 'r2', 'r2p')}
        for j in range(n):
            x = c + j
            lx = mp.log(x)
            dat['fs'].append(x ** (-s))
            dat['ft'].append(x ** (-t))
            dat['mark'].append(-lx)
            dat['lg'].append(lg)
            dat['r2'].append(rz)
            lg += lx
            rz -= lx ** 2
            dat['lgp'].append(lg)
            dat['r2p'].append(rz)
        arrays[c] = dat

    def z(c, *names):
        return z_truncated([arrays[c][name] for name in names], n)

    h_t = mp.zeta(t, b) - mp.zeta(t, a)
    top_one, top_two = {}, {}
    for c in (a, b):
        d = arrays[c]
        lp = [v - mp.log(2 * mp.pi) / 2 for v in d['lgp']]
        top_one[c] = mp.fsum(f * l for f, l in zip(d['ft'], lp))
        top_two[c] = mp.fsum(f * (l ** 2 - r)
                             for f, l, r in zip(d['ft'], lp, d['r2p']))
    h_one = top_one[b] - top_one[a] - zeta0prime[a] * h_t
    h_two = (top_two[b] - top_two[a] - 2 * zeta0prime[a] * h_one
             - (zeta0prime[a] ** 2 - zeta0second[a]) * h_t) / 2
    lhs = (z(b, 'fs', 'mark', 'mark', 'ft')
           - z(a, 'fs', 'mark', 'mark', 'ft')
           - mp.zeta(s, a) * h_two
           - z(a, 'fs', 'mark') * h_one
           - z(a, 'fs', 'mark', 'mark') * h_t)

    def h_two_arrays(left, right):
        zb = z_truncated([left[b], right[b]], n)
        za = z_truncated([left[a], right[a]], n)
        return zb - za - mp.fsum(left[a]) * (mp.fsum(right[b]) - mp.fsum(right[a]))

    fs = {c: arrays[c]['fs'] for c in (a, b)}
    ft = {c: arrays[c]['ft'] for c in (a, b)}
    lower_square = {c: [f * (l ** 2 - r) for f, l, r in
                        zip(arrays[c]['ft'], arrays[c]['lgp'], arrays[c]['r2p'])]
                    for c in (a, b)}
    upper_log = {c: [f * l for f, l in zip(arrays[c]['fs'], arrays[c]['lg'])]
                 for c in (a, b)}
    lower_log = {c: [f * l for f, l in zip(arrays[c]['ft'], arrays[c]['lgp'])]
                 for c in (a, b)}
    upper_square = {c: [f * (l ** 2 + r) for f, l, r in
                        zip(arrays[c]['fs'], arrays[c]['lg'], arrays[c]['r2'])]
                    for c in (a, b)}
    rhs = (h_two_arrays(fs, lower_square) - 2 * h_two_arrays(upper_log, lower_log)
           + h_two_arrays(upper_square, ft)) / 2
    return {"n": n, "absolute_residual": mp.nstr(abs(lhs - rhs), 12),
            "lhs": mp.nstr(lhs, 45), "rhs": mp.nstr(rhs, 45),
            "continuation_rule": "Symmetrize top tails before differentiating."}


def qjet(center, order, x):
    if center == 1:
        return (-1) ** order * mp.stieltjes(order, x)
    return mp.diff(lambda u: mp.zeta(u, x), center, order)


def marked_finite_word(base_s, base_t, centers, orders, b, n):
    """Direct ordered finite sum with labelled markers in the given order."""
    d = len(centers)
    value = mp.mpf(0)
    for indices in combinations(range(n), d + 2):
        indices = indices[::-1]
        y, z = b + indices[0], b + indices[-1]
        term = y ** (-base_s) * z ** (-base_t)
        for j, center, order in zip(indices[1:-1], centers, orders):
            x = b + j
            term *= x ** (-center) * (-mp.log(x)) ** order
        value += term
    return value


def check_finite_marked(centers, orders, b, n):
    s = mp.mpc('2.3', '.14')
    t = mp.mpc('1.7', '-.09')
    k = len(centers)
    lhs = mp.mpf(0)
    for permutation in permutations(range(k)):
        lhs += marked_finite_word(s, t,
                                 tuple(centers[j] for j in permutation),
                                 tuple(orders[j] for j in permutation), b, n)
    jets = {}

    def gap(block, y, z):
        center = sum(centers[j] for j in block)
        order = sum(orders[j] for j in block)
        key = center, order, y, z
        if key not in jets:
            jets[key] = qjet(center, order, z + 1) - qjet(center, order, y)
        return jets[key]

    rhs = mp.mpf(0)
    for low, high in combinations(range(n), 2):
        y, z = b + high, b + low
        poly = mp.mpf(0)
        for partition in partitions(range(k)):
            coefficient = (-1) ** (k - len(partition))
            for block in partition:
                coefficient *= factorial(len(block) - 1)
            term = coefficient
            for block in partition:
                term *= gap(block, y, z)
            poly += term
        rhs += y ** (-s) * z ** (-t) * poly
    residual = abs(lhs - rhs)
    assert residual < mp.mpf('1e-40'), residual
    return {"centers": [str(c) for c in centers], "orders": list(orders),
            "lower_endpoint": str(b), "interval_length": n,
            "absolute_residual": mp.nstr(residual, 12),
            "value": mp.nstr(lhs, 45)}


def main():
    started = time.time()
    mp.mp.dps = 60
    symbolic = [check_symbolic(k) for k in range(1, 6)]
    generic = [check_noninteger_generic(n) for n in (80, 160)]
    zero_marks = [check_noninteger_log_pair(n) for n in (80, 160)]
    assert mp.mpf(generic[-1]["absolute_residual"]) < mp.mpf('1e-25')
    assert mp.mpf(zero_marks[-1]["absolute_residual"]) < mp.mpf('1e-20')
    finite = [
        check_finite_marked((mp.mpf(0),) * 2, (1, 1), mp.mpf('1.25'), 6),
        check_finite_marked((mp.mpf(0),) * 3, (1, 1, 1), mp.mpf('1.25'), 6),
        check_finite_marked((mp.mpf(-1),) * 2, (1, 1), mp.mpf('1.25'), 6),
        check_finite_marked((mp.mpf(0), mp.mpf(1)), (1, 1), mp.mpf('1.25'), 5),
        check_finite_marked((mp.mpf('.5'),) * 2, (1, 1), mp.mpf('1.25'), 5),
    ]
    result = {"precision_decimal_digits": mp.mp.dps,
              "symbolic_partition_checks": symbolic,
              "noninteger_endpoint_checks": generic,
              "noninteger_zero_marker_checks": zero_marks,
              "finite_transverse_checks": finite,
              "wall_seconds": round(time.time() - started, 3),
              "scope": "Diagnostics only; analytic continuation is proved separately."}
    output = Path(__file__).with_name('marked_gap_verification.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
