#!/usr/bin/env python3
"""Exact finite audits for Aligned Fragments and Constrained Crossover.

Python 3.10+, standard library only. These tests audit finite instances; they
are not proof-assistant certificates or substitutes for the article's proofs.
Run from any directory: python code/verify.py
"""
from __future__ import annotations
from collections import deque
from itertools import product
from math import comb
from pathlib import Path
import json
import time

INF = 10**9
COUNTS: dict[str, int] = {}


def check(condition: bool, message: str, category: str) -> None:
    """Checks stay enabled under python -O."""
    COUNTS[category] = COUNTS.get(category, 0) + 1
    if not condition:
        raise AssertionError(message)


def words(alphabet: str, n: int) -> list[str]:
    return [''.join(t) for t in product(alphabet, repeat=n)]


def bits(mask: int) -> list[int]:
    ans = []
    while mask:
        b = mask & -mask
        ans.append(b.bit_length()-1)
        mask ^= b
    return ans


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError('ceil_log2 requires a positive integer')
    return (n-1).bit_length()


def rank_from_sources(w: str, sources: list[str] | set[str]) -> int:
    n = len(w)
    if any(len(u) != n for u in sources):
        raise ValueError('All source words must have the target length')
    if not n:
        return 1 if '' in sources else INF
    d = [0] + [INF]*n
    for j in range(1, n+1):
        for i in range(j):
            if d[i] < INF and any(u[i:j] == w[i:j] for u in sources):
                d[j] = min(d[j], d[i]+1)
    return d[n]


def exhaustive_slices() -> dict[str, int]:
    slice_count = target_count = 0
    for n in range(5):
        ws = words('01', n)
        size = len(ws)
        index = {w: i for i, w in enumerate(ws)}
        # Each mask below is a set of complete source words, not an assignment
        # mask. Interval compatibility is one exact bitwise intersection.
        support = []
        for w in ws:
            support.append([[sum(1 << k for k, u in enumerate(ws)
                                 if u[i:j] == w[i:j])
                             for i in range(j)] for j in range(n+1)])
        pair_children = [[sum(1 << k for k in set(
            index[u[:c]+v[c:]] for c in range(n+1))) for v in ws] for u in ws]
        rank_cache = []
        cross_cache = []
        for seed in range(1 << size):
            rows = []
            for wi in range(size):
                if not n:
                    rows.append(1 if seed else INF)
                    continue
                d = [0] + [INF]*n
                for j in range(1, n+1):
                    best = INF
                    for i in range(j):
                        if seed & support[wi][j][i]:
                            best = min(best, d[i]+1)
                    d[j] = best
                rows.append(min(d[n], INF))
            rank_cache.append(rows)
            present = bits(seed)
            cross = 0
            for i in present:
                for j in present:
                    cross |= pair_children[i][j]
            cross_cache.append(cross)
        for seed in range(1 << size):
            slice_count += 1
            ranks = rank_cache[seed]
            target_count += size
            finite = [r for r in ranks if r < INF]
            spectrum = set(finite)
            R = max(finite, default=0)
            check(spectrum == set(range(1, R+1)),
                  f'No-gap n={n} seed={seed}', 'rank_spectrum')
            present = bits(seed)
            hull = 0
            if present:
                for wi, w in enumerate(ws):
                    if all(any(ws[s][i] == w[i] for s in present) for i in range(n)):
                        hull |= 1 << wi
            check(hull == sum(1 << i for i, r in enumerate(ranks) if r < INF),
                  f'Hull n={n} seed={seed}', 'hull')
            cross = cross_cache[seed]
            for wi, r in enumerate(ranks):
                expected = (r+1)//2 if r < INF else INF
                check(rank_cache[cross][wi] == expected,
                      f'Contraction n={n}, seed={seed}, w={ws[wi]}', 'contraction')
            stage = seed
            h = ceil_log2(R) if R else 0
            for k in range(max(1, ceil_log2(max(1, n)))+1):
                expected = sum(1 << i for i, r in enumerate(ranks) if r <= 2**k)
                check(stage == expected,
                      f'Generation n={n}, seed={seed}, k={k}', 'generation')
                if k == h:
                    check(stage == hull,
                          f'Stabilization n={n}, seed={seed}', 'stabilization')
                stage = cross_cache[stage]
            # Frozen-source iteration permits both crossover children, but
            # requires one parent to remain in the original seed set.
            frozen = seed
            for k in range(max(1, n)):
                expected = sum(1 << i for i, r in enumerate(ranks) if r <= k+1)
                check(frozen == expected,
                      f'Frozen generation n={n}, seed={seed}, k={k}', 'frozen_generation')
                nxt = 0
                for i in present:
                    for j in bits(frozen):
                        nxt |= pair_children[i][j] | pair_children[j][i]
                frozen = nxt
        print(f'All binary length-{n} seed sets: {1 << size:,} PASS', flush=True)
    return {'seed_slices': slice_count, 'target_rank_queries': target_count}


class DFA:
    """Complete DFA. Transitions are rows indexed by alphabet position."""
    def __init__(self, alphabet: str, trans: tuple[tuple[int, ...], ...], final: set[int]):
        self.alphabet, self.trans, self.final = alphabet, trans, final
        self.s = len(trans)
        self.ai = {a: i for i, a in enumerate(alphabet)}
        if any(len(row) != len(alphabet) or any(q < 0 or q >= self.s for q in row)
               for row in trans):
            raise ValueError('Invalid complete transition table')

    def step(self, q: int, a: str) -> int:
        return self.trans[q][self.ai[a]]

    def accept(self, w: str) -> bool:
        q = 0
        for a in w:
            q = self.step(q, a)
        return q in self.final

    def reach(self, n: int) -> tuple[list[set[int]], list[set[int]]]:
        U = [{0}]
        for _ in range(n):
            U.append({r for q in U[-1] for r in self.trans[q]})
        V = [set() for _ in range(n+1)]
        V[n] = set(self.final)
        for i in range(n-1, -1, -1):
            V[i] = {q for q in range(self.s) if any(r in V[i+1] for r in self.trans[q])}
        return U, V

    def rank(self, w: str) -> int:
        n = len(w)
        if n == 0:
            return 1 if self.accept(w) else INF
        U, V = self.reach(n)
        d = [0] + [INF]*n
        for i in range(n):
            active = set(U[i])
            for j in range(i+1, n+1):
                active = {self.step(q, w[j-1]) for q in active}
                if active & V[j]:
                    d[j] = min(d[j], d[i]+1)
        return min(INF, d[n])

    def distance(self, w: str) -> int:
        """The article's 0/1 automaton, with its unique accepting V sequence.

        V_i=Pre(V_{i+1}), V_n=F makes every successful nondeterministic
        sequence of right-boundary guesses exactly the sequence used here.
        """
        n = len(w)
        U, V = self.reach(n)
        cost = {0: 0}
        for i, a in enumerate(w):
            nxt: dict[int, int] = {}
            for q, c in cost.items():
                r = self.step(q, a)
                nxt[r] = min(nxt.get(r, INF), c)
                if q in V[i]:
                    for p in U[i]:
                        r = self.step(p, a)
                        nxt[r] = min(nxt.get(r, INF), c+1)
            cost = nxt
        return min((c for q, c in cost.items() if q in self.final), default=INF)

    def closure_witness(self) -> str | None:
        """BFS in the 2*s^3-state one-step violation graph."""
        start = (0, 0, 0, 0)
        queue = deque([start])
        pred: dict[tuple[int, ...], tuple[tuple[int, ...], str] | None] = {start: None}
        while queue:
            p, q, r, phase = state = queue.popleft()
            if p in self.final and q in self.final and r not in self.final:
                out = []
                while pred[state] is not None:
                    state, letter = pred[state]  # type: ignore[misc]
                    out.append(letter)
                return ''.join(reversed(out))
            edges = []
            if phase == 0:
                edges.append(((p, q, r, 1), ''))
            for a in self.alphabet:
                for b in self.alphabet:
                    np = self.step(p, a if phase == 0 else b)
                    nq = self.step(q, b if phase == 0 else a)
                    edges.append(((np, nq, self.step(r, a), phase), a))
            for nxt, letter in edges:
                if nxt not in pred:
                    pred[nxt] = (state, letter)
                    queue.append(nxt)
        return None


def regular_tests() -> dict[str, int]:
    count = query_count = 0
    for flat in product(range(2), repeat=4):
        trans = (flat[:2], flat[2:])
        for fmask in range(4):
            dfa = DFA('01', trans, set(bits(fmask)))
            count += 1
            witness = dfa.closure_witness()
            finite_failure = False
            for n in range(7):
                universe = words('01', n)
                seeds = [u for u in universe if dfa.accept(u)]
                for w in universe:
                    query_count += 1
                    rho = rank_from_sources(w, seeds)
                    check(dfa.rank(w) == rho, 'DFA interval rank mismatch', 'dfa_rank')
                    expected = rho-1 if rho < INF else INF
                    check(dfa.distance(w) == expected,
                          'Distance automaton mismatch', 'distance_automaton')
                    if rho == 2 and not dfa.accept(w):
                        finite_failure = True
            check(not finite_failure or witness is not None,
                  'Violation graph missed finite witness', 'dfa_violation')
            if witness is not None:
                check(dfa.rank(witness) == 2 and not dfa.accept(witness),
                      'Invalid graph witness', 'dfa_violation')
                check(len(witness) <= 2*dfa.s**3-1,
                      'Witness length bound', 'dfa_violation')
    return {'two_state_binary_dfas': count, 'target_queries': query_count}


def block_tests() -> dict[str, object]:
    # G is {0,1,@}* minus {00}; B=G(#G)*. State 4 is dead.
    dfa = DFA('01@#', ((1, 3, 3, 0), (2, 3, 3, 0),
                       (3, 3, 3, 4), (3, 3, 3, 0), (4, 4, 4, 4)), {0, 1, 3})
    receipts = []
    for r in range(1, 65):
        w = '#'.join(['00']*r)
        rho = dfa.rank(w)
        check(rho == r+1, f'Block amplification r={r}', 'block_amplification')
        check(dfa.distance(w) == r, f'Block distance r={r}', 'block_amplification')
        receipts.append({'blocks': r, 'length': len(w), 'rank': rho,
                         'generation': ceil_log2(rho)})
    for r in (1, 2, 3):
        w = '#'.join(['00']*r)
        seeds = [u for u in words('01@#', len(w)) if dfa.accept(u)]
        check(rank_from_sources(w, seeds) == r+1,
              'Independent full-alphabet block enumeration', 'block_full_enumeration')
    # Universal one-step guard repair, including the shortest forbidden word.
    guard_cases = 0
    for n in range(2, 10):
        for x in words('01', n-2):
            w = '00'+x
            u = w[0]+'@'+w[2:]
            v = '@'+w[1:]
            check('@' in u and '@' in v and u[:1]+v[1:] == w,
                  'Guard repair identity', 'guard_repair')
            guard_cases += 1
    return {'guard_repairs': guard_cases, 'block_receipts': receipts,
            'full_alphabet_enumerated_lengths': [2, 5, 8]}


def seed_q(w: str, q: int) -> bool:
    if w.count('1') == 0:
        return True
    if w.count('1') != 1:
        return False
    i = w.index('1')
    j = len(w)-1-i
    return j >= (q-1)*i+q-1 or i >= (q-1)*j+q-1


def family_tests() -> dict[str, int]:
    queries = 0
    for q in range(3, 8):
        for n in range(13):
            universe = words('01', n)
            seeds = [u for u in universe if seed_q(u, q)]
            m, r = divmod(n, q)
            histogram: dict[int, int] = {}
            for w in universe:
                queries += 1
                inside = '1' not in w[m:n-m]
                expected = max(1, w.count('1')) if inside else INF
                rho = rank_from_sources(w, seeds)
                check(rho == expected, f'Family q={q}, w={w}', 'family_rank')
                if inside:
                    histogram[w.count('1')] = histogram.get(w.count('1'), 0)+1
            check(histogram == {j: comb(2*m, j) for j in range(2*m+1)},
                  'Weighted hull enumerator', 'family_count')
            check(sum(histogram.values()) == 4**m,
                  'Hull length enumerator', 'family_count')
            for k in range(4):
                direct = sum(v for j, v in histogram.items() if j <= 2**k)
                expected = sum(comb(2*m, j) for j in range(min(2*m, 2**k)+1))
                check(direct == expected, 'Finite generation count', 'family_count')
    # Exact recurrence certificates for the claimed reduced denominator.
    for q in range(3, 8):
        for k in range(5):
            D = 2**k
            order = q*D+1
            nmax = 3*order + 2*q
            a = [sum(comb(2*(n//q), j)
                     for j in range(min(2*(n//q), D)+1)) for n in range(nmax+1)]
            den = [0]*(order+1)
            for j in range(D+1):
                c = (-1)**j*comb(D, j)
                den[q*j] += c
                den[q*j+1] -= c
            numerator = [sum(den[j]*a[n-j] for j in range(min(n, order)+1))
                         for n in range(nmax+1)]
            check(all(v == 0 for v in numerator[order+q:]),
                  'Finite-level recurrence', 'recurrence')
            # A degree-D polynomial has nonzero Dth difference and vanishing
            # (D+1)st difference. This tests the no-extra-cancellation ingredient.
            b = [sum(comb(2*t, j) for j in range(min(2*t, D)+1)) for t in range(D+2)]
            for _ in range(D):
                b = [y-x for x, y in zip(b, b[1:])]
            check(b == [2**D, 2**D], 'Exact polynomial degree', 'recurrence')
    return {'binary_target_queries': queries, 'q_range': [3, 7], 'max_length': 12,
            'recurrence_parameter_pairs': 25}


def main() -> None:
    start = time.perf_counter()
    result: dict[str, object] = {'status': 'RUNNING', 'scope': 'finite exact audits, not formal proofs'}
    result['exhaustive_slices'] = exhaustive_slices()
    result['regular'] = regular_tests()
    print('Regular-input and distance-automaton audits PASS', flush=True)
    result['blocks'] = block_tests()
    print('Guard and block-amplification audits PASS', flush=True)
    result['family'] = family_tests()
    result['checks_by_category'] = COUNTS
    result['total_checks'] = sum(COUNTS.values())
    result['elapsed_seconds'] = round(time.perf_counter()-start, 3)
    result['status'] = 'PASS'
    out = Path(__file__).resolve().parent.parent/'data'/'verification.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status', 'total_checks', 'elapsed_seconds')}, indent=2))
    print(f'Receipt: {out}')


if __name__ == '__main__':
    main()
