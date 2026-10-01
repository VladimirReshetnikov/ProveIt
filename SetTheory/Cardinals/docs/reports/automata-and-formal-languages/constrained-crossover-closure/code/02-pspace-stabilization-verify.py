#!/usr/bin/env python3
"""Exact finite audits for Finite Crossover Stabilization Is PSPACE-Complete.

Python >=3.10, standard library only. Mathematical proofs are in article.tex.
The explicit phase/subset search below is a reference implementation, NOT
an implementation of the polynomial-space resource bound in the article.
Run from any directory; output location is controlled by --output.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
from math import lcm
from pathlib import Path
import json
import platform
import random
import time

Word = tuple[int, ...]


def bits(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


@dataclass(frozen=True)
class NFA:
    """rows[q][a] is the destination bitset; initial/final are bitsets."""
    rows: tuple[tuple[int, ...], ...]
    initial: int
    final: int

    def __post_init__(self):
        if not self.rows or not self.rows[0]:
            raise ValueError("A nonempty state set and alphabet are required")
        n, k = len(self.rows), len(self.rows[0])
        if any(len(row) != k for row in self.rows):
            raise ValueError("Transition rows must have equal lengths")
        if any(v < 0 or v >= 1 << n for row in self.rows for v in row):
            raise ValueError("Invalid transition bitset")
        if not (0 <= self.initial < 1 << n and 0 <= self.final < 1 << n):
            raise ValueError("Invalid initial/final bitset")

    @property
    def n(self): return len(self.rows)

    @property
    def k(self): return len(self.rows[0])

    @property
    def deterministic(self):
        return all(v.bit_count() <= 1 for row in self.rows for v in row)

    def post(self, mask: int, a: int | None = None) -> int:
        ans = 0
        for q in bits(mask):
            if a is None:
                for val in self.rows[q]: ans |= val
            else:
                ans |= self.rows[q][a]
        return ans

    def pre(self, mask: int) -> int:
        ans = 0
        for q, row in enumerate(self.rows):
            if any(val & mask for val in row): ans |= 1 << q
        return ans

    def accepts(self, word: Word) -> bool:
        z = self.initial
        for a in word: z = self.post(z, a)
        return bool(z & self.final)

    def layers(self, n: int):
        p, r = [self.initial], [self.final]
        for _ in range(n):
            p.append(self.post(p[-1]))
            r.append(self.pre(r[-1]))
        return p, r

    def rank(self, word: Word) -> int | None:
        """Shortest aligned-fragment partition, via exact-length paths."""
        n = len(word)
        if n == 0: return 1 if self.initial & self.final else None
        p, r = self.layers(n)
        dp = [n + 1] * (n + 1)
        dp[0] = 0
        for i in range(n):
            if dp[i] > n: continue
            z = p[i]
            for j in range(i + 1, n + 1):
                z = self.post(z, word[j - 1])
                if z & r[n - j]: dp[j] = min(dp[j], dp[i] + 1)
                if not z: break
        return None if dp[n] > n else dp[n]

    def accepted_word(self, n: int) -> Word:
        _, r = self.layers(n)
        start = self.initial & r[n]
        if not start: raise ValueError("No accepted word of requested length")
        q = next(bits(start))
        out = []
        for pos in range(n):
            for a in range(self.k):
                dest = self.rows[q][a] & r[n - pos - 1]
                if dest:
                    out.append(a)
                    q = next(bits(dest))
                    break
            else: raise AssertionError("Broken accepting-path reconstruction")
        return tuple(out)


class Periodic:
    """Explicit least cycle of (P_i,R_i), used only on small automata."""
    def __init__(self, automaton: NFA):
        self.a = automaton
        seen, seq = {}, []
        pair = automaton.initial, automaton.final
        while pair not in seen:
            seen[pair] = len(seq)
            seq.append(pair)
            pair = automaton.post(pair[0]), automaton.pre(pair[1])
        self.t = seen[pair]
        self.p = len(seq) - self.t
        self.seq = seq
        self.live = [r for r in range(self.p)
                     if self.at(self.rep(r))[0] & automaton.final]

    def at(self, n: int):
        if n >= len(self.seq): n = self.t + (n - self.t) % self.p
        return self.seq[n]

    def rep(self, phase: int) -> int:
        return self.t + (phase - self.t) % self.p

    def system(self, r: int):
        s = [self.at(self.rep(j))[0] & self.at(self.rep(r - j))[1]
             for j in range(self.p)]
        c = [tuple(a for a in range(self.a.k)
                   if self.a.post(s[j], a) & s[(j + 1) % self.p])
             for j in range(self.p)]
        if r in self.live:
            assert all(s) and all(c)
        return s, c

    def forbidden(self):
        """Return (live residue, start phase, shortest-at-that-start word)."""
        for r in self.live:
            s, c = self.system(r)
            for start in range(self.p):
                root = start, s[start]
                pred = {root: None}
                queue = deque([root])
                while queue:
                    j, z = queue.popleft()
                    for a in c[j]:
                        j1 = (j + 1) % self.p
                        zz = self.a.post(z, a) & s[j1]
                        node = j1, zz
                        if node in pred: continue
                        pred[node] = ((j, z), a)
                        if zz == 0:
                            rev = []
                            while pred[node] is not None:
                                node, aa = pred[node]
                                rev.append(aa)
                            word = tuple(reversed(rev))
                            assert 2 <= len(word) <= self.p * (1 << self.a.n)
                            return r, start, word
                        queue.append(node)
        return None

    def safe_core_stabilizes(self):
        if not self.a.deterministic:
            raise ValueError("Safe-core test requires statewise determinism")
        for r in self.live:
            s, c = self.system(r)
            u = s[:]
            while True:
                v = [sum(1 << q for q in bits(u[j])
                         if all(self.a.rows[q][a] & u[(j+1) % self.p]
                                for a in c[j]))
                     for j in range(self.p)]
                if u == v: break
                u = v
            if not any(u): return False
            assert all(u)
        return True

    def pump(self, obstruction, copies: int) -> Word:
        r, start, v = obstruction
        _, c = self.system(r)
        b = list(v)
        while len(b) % self.p:
            b.append(c[(start + len(b)) % self.p][0])
        # Positive boundaries avoid a vacuous baseline when the cycle starts at 0.
        base = max(1, self.t)
        left = base + (start - base) % self.p
        right = base + (r - start - base) % self.p
        accepted = self.a.accepted_word(left + right)
        return accepted[:left] + tuple(b) * copies + accepted[left:]


def finite_ranks(seed: set[Word], n: int, k: int):
    """Independent exhaustive substring oracle; no automaton path formulas."""
    if n == 0: return {(): 1 if () in seed else None}
    allowed = {(i, j): {w[i:j] for w in seed}
               for i in range(n) for j in range(i + 1, n + 1)}
    out = {}
    for w in product(range(k), repeat=n):
        dp = [0] + [n + 1] * n
        for j in range(1, n + 1):
            dp[j] = min((dp[i] + 1 for i in range(j)
                         if w[i:j] in allowed[i, j]), default=n+1)
        out[w] = dp[n] if dp[n] <= n else None
    return out


def crossover(seed: set[Word], n: int):
    return {x[:i] + y[i:] for x in seed for y in seed for i in range(n + 1)}


def binary_unary_extension(a: NFA) -> NFA:
    """Disjoint union with 0* and 1*; expects all states initial and final."""
    assert a.k == 2 and a.initial == a.final == (1 << a.n) - 1
    rows = a.rows + ((1 << a.n, 0), (0, 1 << (a.n+1)))
    return NFA(rows, (1 << (a.n+2))-1, (1 << (a.n+2))-1)


def universal(a: NFA) -> bool:
    seen, queue = {a.initial}, deque([a.initial])
    while queue:
        z = queue.popleft()
        if not z & a.final: return False
        for c in range(a.k):
            zz = a.post(z, c)
            if zz not in seen:
                seen.add(zz)
                queue.append(zz)
    return True


def unary_reachability_period_audit(counts: Counter):
    # Every directed graph on 1..3 labelled vertices, all initial/final sets.
    for n in range(1, 4):
        period = lcm(*range(1, n + 3))
        transient = 2 * (n+2)**2 + 2 * (n+2)
        for masks in product(range(1 << n), repeat=n):
            rows = tuple((v,) for v in masks)
            for initial in range(1 << n):
                a = NFA(rows, initial, initial)
                per = Periodic(a)
                for j in range(transient, transient + per.p):
                    assert per.at(j) == per.at(j + period)
                    counts['unary_period_equalities'] += 1
                counts['unary_graph_subset_cases'] += 1



def complement_singleton(x: Word) -> NFA:
    """Complete binary DFA for all words other than x."""
    other = len(x) + 1
    rows = []
    for j in range(len(x) + 1):
        rows.append(tuple(1 << (j+1 if j < len(x) and c == x[j] else other)
                          for c in range(2)))
    rows.append((1 << other, 1 << other))
    return NFA(tuple(rows), 1, ((1 << len(rows))-1) ^ (1 << len(x)))


def delimiter_dfa(a: NFA) -> NFA:
    """Complete DFA for B(K), with symbols 2=@ and 3=#, from a binary DFA."""
    assert a.k == 2 and a.initial.bit_count() == 1
    assert all(v.bit_count() == 1 for row in a.rows for v in row)
    pre, guard, sink = a.n, a.n+1, a.n+2
    rows = [row + (1 << guard, a.initial if a.final >> q & 1 else 1 << sink)
            for q, row in enumerate(a.rows)]
    rows += [(1 << pre, 1 << pre, 1 << pre, a.initial),
             (1 << guard, 1 << guard, 1 << guard, a.initial),
             (1 << sink,) * 4]
    return NFA(tuple(rows), 1 << pre, ((1 << len(rows))-1) ^ (1 << sink))


def worked_examples(counts: Counter):
    # Every omitted binary word of lengths 0..5; r=1..8.
    for n in range(6):
        for x in product(range(2), repeat=n):
            a = delimiter_dfa(complement_singleton(x))
            for copies in range(1, 9):
                target = (3,) + (x + (3,)) * copies
                assert a.rank(target) == copies + 1
                counts['exact_delimiter_rank_checks'] += 1
            for length in range(1, 9):
                for pos in range(length):
                    for c in range(4):
                        w = (2,) * pos + (c,) + (2,) * (length-pos-1)
                        assert a.accepts(w)
                        counts['delimiter_coordinate_witness_checks'] += 1
    b = delimiter_dfa(NFA(((1, 1),), 1, 1))
    assert universal(b) and Periodic(b).forbidden() is None
    # Even lengths or unary words, using four states.
    parity = NFA(((2, 2), (1, 1), (4, 0), (0, 8)), 13, 13)
    for n in range(1, 11):
        for w in product(range(2), repeat=n):
            runs = 1 + sum(w[j] != w[j-1] for j in range(1, n))
            assert parity.rank(w) == (1 if n % 2 == 0 else runs)
            counts['parity_example_rank_checks'] += 1
    assert Periodic(parity).forbidden() is not None
    # Boundary-repair example, independently from explicit finite seeds.
    for n in range(8):
        seed = {w for w in product(range(2), repeat=n)
                if not w or w[0] == 0 or w[-1] == 0}
        ranks = finite_ranks(seed, n, 2)
        for w, rank in ranks.items():
            expected = (1 if w in seed else None if n < 2 else 2)
            assert rank == expected
            counts['boundary_example_rank_checks'] += 1
    # Universal NFA with no vertexwise safe core (safety is not sufficient as a test).
    nondet = NFA(((3, 0), (0, 3)), 3, 3)
    assert universal(nondet) and Periodic(nondet).forbidden() is None


def run_suite():
    start = time.monotonic()
    counts = Counter()
    verdicts = Counter()
    examples = []
    # All labelled 2-state, 2-letter NFAs, every initial/final subset.
    for flat in product(range(4), repeat=4):
        rows = (flat[:2], flat[2:])
        for initial in range(4):
            for final in range(4):
                a = NFA(rows, initial, final)
                per = Periodic(a)
                obstruction = per.forbidden()
                stable = obstruction is None
                verdicts['nfa2_stable' if stable else 'nfa2_unstable'] += 1
                counts['nfa2_automata'] += 1
                if a.deterministic:
                    assert per.safe_core_stabilizes() == stable
                    counts['partial_deterministic_core_comparisons'] += 1
                for n in range(6):
                    seeds = {w for w in product(range(2), repeat=n) if a.accepts(w)}
                    independent = finite_ranks(seeds, n, 2)
                    for w, expected in independent.items():
                        actual = a.rank(w)
                        assert actual == expected, (a, w, actual, expected)
                        counts['independent_rank_comparisons'] += 1
                        if stable and actual is not None:
                            assert actual <= 2 * per.t + 1, (a, per.t, w, actual)
                            counts['stable_rank_bound_checks'] += 1
                if obstruction:
                    for copies in (1, 2, 4, 8):
                        w = per.pump(obstruction, copies)
                        rank = a.rank(w)
                        assert rank is not None and rank >= copies + 1
                        counts['pumped_witness_checks'] += 1
                    if len(examples) < 8:
                        examples.append({'rows': rows, 'I': initial, 'F': final,
                                         'transient': per.t, 'period': per.p,
                                         'obstruction': obstruction})
    print('All 4096 two-state binary NFAs audited.', flush=True)
    # Complete 3-state binary DFAs, fixed initial state 0.
    for flat in product(range(3), repeat=6):
        rows = tuple(tuple(1 << q for q in flat[2*j:2*j+2]) for j in range(3))
        for final in range(8):
            a = NFA(rows, 1, final)
            per = Periodic(a)
            obstruction = per.forbidden()
            stable = obstruction is None
            assert per.safe_core_stabilizes() == stable
            counts['dfa3_core_comparisons'] += 1
            verdicts['dfa3_stable' if stable else 'dfa3_unstable'] += 1
            if obstruction:
                assert len(obstruction[2]) <= per.p * a.n**2
                for copies in (1, 3):
                    rank = a.rank(per.pump(obstruction, copies))
                    assert rank is not None and rank >= copies+1
                    counts['pumped_witness_checks'] += 1
            else:
                for w in product(range(2), repeat=6):
                    rank = a.rank(w)
                    assert rank is None or rank <= 2 * per.t + 1
                    counts['stable_dfa3_rank_checks'] += 1
    print('All 5832 three-state binary DFAs audited.', flush=True)
    # All-initial/all-final binary hardness transformation.
    for flat in product(range(4), repeat=4):
        a = NFA((flat[:2], flat[2:]), 3, 3)
        b = binary_unary_extension(a)
        assert universal(a) == universal(b)
        assert universal(a) == (Periodic(b).forbidden() is None)
        for n in range(1, 9):
            for c in range(2): assert b.accepts((c,) * n)
        counts['binary_hardness_reduction_cases'] += 1
    # Finite seeds: literal crossover operation vs fragment rank, all sets n<=3.
    for n in range(4):
        words = list(product(range(2), repeat=n))
        for mask in range(1 << len(words)):
            seed = {words[i] for i in range(len(words)) if mask >> i & 1}
            ranks = finite_ranks(seed, n, 2)
            current = seed
            for gen in range(4):
                expected = {w for w, rank in ranks.items()
                            if rank is not None and rank <= 2**gen}
                assert current == expected
                current = crossover(current, n)
                counts['literal_generation_comparisons'] += 1
            counts['finite_seed_sets'] += 1
    # Sharp logarithmic-generation lower family (one 1 in a word of length m).
    lower_family = []
    for m in range(1, 25):
        # Layered partial DFA with states (position, used-one), plus sink.
        rows = []
        sink = 2*(m+1)
        for pos in range(m+1):
            for used in range(2):
                if pos == m: rows.append((1 << sink, 1 << sink))
                else:
                    rows.append((1 << (2*(pos+1)+used),
                                 1 << (2*(pos+1)+1) if not used else 1 << sink))
        rows.append((1 << sink, 1 << sink))
        a = NFA(tuple(rows), 1, 1 << (2*m+1))
        assert a.rank((1,) * m) == m
        assert Periodic(a).forbidden() is None
        lower_family.append({'m':m, 'states':a.n, 'rank':m,
                             'parallel_depth':(m-1).bit_length()})
        counts['lower_family_cases'] += 1
    # Longer random NFAs (seeded samples, not exhaustive).
    rng = random.Random(20260930)
    for _ in range(200):
        n = rng.randrange(3, 7)
        rows = tuple(tuple(rng.randrange(1 << n) for _ in range(2)) for _ in range(n))
        a = NFA(rows, rng.randrange(1 << n), rng.randrange(1 << n))
        per = Periodic(a)
        ob = per.forbidden()
        for _ in range(20):
            w = tuple(rng.randrange(2) for _ in range(rng.randrange(1, 21)))
            rank = a.rank(w)
            if ob is None: assert rank is None or rank <= 2*per.t+1
            counts['sampled_rank_checks'] += 1
        if ob:
            rank = a.rank(per.pump(ob, 7))
            assert rank is not None and rank >= 8
            counts['pumped_witness_checks'] += 1
        counts['sampled_nfas'] += 1
    unary_reachability_period_audit(counts)
    worked_examples(counts)
    receipt = {
        'status':'PASS', 'python':platform.python_version(),
        'elapsed_seconds':round(time.monotonic()-start, 3),
        'random_seed':20260930,
        'counts':dict(sorted(counts.items())),
        'verdicts':dict(sorted(verdicts.items())),
        'examples':examples, 'lower_family':lower_family,
        'limitations':[
            'Finite tests do not prove all-state or all-length statements.',
            'The phase/subset reference solver stores explicit graphs; it is not the PSPACE implementation.',
            'Ranks are cross-checked independently only in the stated finite ranges.',
            'The published unary progression theorem and PSPACE-hardness source are not reproved by this code.',
            'No Lean or Rocq checking is performed.'
        ]
    }
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    receipt = run_suite()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('examples','lower_family')}, indent=2))
    print(f'Receipt: {args.output}')


if __name__ == '__main__':
    main()
