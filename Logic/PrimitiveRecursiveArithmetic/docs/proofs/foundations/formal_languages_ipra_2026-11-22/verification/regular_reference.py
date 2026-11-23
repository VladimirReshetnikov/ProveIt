#!/usr/bin/env python3
"""Finite automata reference constructions and independent finite cross-checks.

This is executable supporting evidence, not a formal proof or an iPRA checker.
All algorithms have the bounds justified in chapters/regular.tex. No external
Python packages are required. Run: python3 verification/regular_reference.py
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from collections import deque
import json


@dataclass(frozen=True)
class DFA:
    k: int
    table: tuple[tuple[int, ...], ...]
    start: int
    finals: frozenset[int]

    @property
    def n(self):
        return len(self.table)

    def validate(self):
        assert self.k >= 1 and self.n >= 1 and 0 <= self.start < self.n
        assert all(len(row) == self.k for row in self.table)
        assert all(0 <= q < self.n for row in self.table for q in row)
        assert all(0 <= q < self.n for q in self.finals)
        return self

    def run(self, word, state=None):
        q = self.start if state is None else state
        for a in word:
            q = self.table[q][a]
        return q

    def accepts(self, word):
        return self.run(word) in self.finals


@dataclass(frozen=True)
class ENFA:
    k: int
    n: int
    starts: frozenset[int]
    finals: frozenset[int]
    edges: frozenset[tuple[int, int | None, int]]

    def closure(self, states):
        current = set(states)
        for _ in range(self.n):
            current |= {r for q, a, r in self.edges if a is None and q in current}
        return frozenset(current)

    def accepts_graph(self, word):
        """Independent finite configuration-graph semantics, not subset code."""
        reached = {(q, 0) for q in self.starts}
        todo = deque(reached)
        while todo:
            q, i = todo.popleft()
            for source, a, target in self.edges:
                if source != q:
                    continue
                if a is None:
                    nxt = (target, i)
                elif i < len(word) and a == word[i]:
                    nxt = (target, i + 1)
                else:
                    continue
                if nxt not in reached:
                    reached.add(nxt)
                    todo.append(nxt)
        return any((q, len(word)) in reached for q in self.finals)


def as_enfa(m):
    return ENFA(m.k, m.n, frozenset([m.start]), m.finals,
                frozenset((q, a, m.table[q][a])
                          for q in range(m.n) for a in range(m.k)))


def determinize(m):
    subsets = tuple(frozenset(q for q in range(m.n) if bits >> q & 1)
                    for bits in range(1 << m.n))
    def code(states):
        return sum(1 << q for q in states)
    rows = []
    for states in subsets:
        rows.append(tuple(code(m.closure(r for q, b, r in m.edges
                                         if b == a and q in states))
                          for a in range(m.k)))
    # States reached from the initial closure remain epsilon-closed.
    return DFA(m.k, tuple(rows), code(m.closure(m.starts)),
               frozenset(i for i, states in enumerate(subsets)
                         if states & m.finals)).validate()


def combine(a, b, boolean):
    assert a.k == b.k
    return DFA(a.k,
               tuple(tuple(a.table[q][c] * b.n + b.table[r][c]
                           for c in range(a.k))
                     for q in range(a.n) for r in range(b.n)),
               a.start * b.n + b.start,
               frozenset(q * b.n + r
                         for q in range(a.n) for r in range(b.n)
                         if boolean(q in a.finals, r in b.finals))).validate()


def reverse(m):
    a = as_enfa(m)
    return ENFA(a.k, a.n, a.finals, a.starts,
                frozenset((r, c, q) for q, c, r in a.edges))


def concatenate(a, b):
    a, b = as_enfa(a), as_enfa(b)
    assert a.k == b.k
    off = a.n
    edges = set(a.edges) | {(q + off, c, r + off) for q, c, r in b.edges}
    edges |= {(q, None, r + off) for q in a.finals for r in b.starts}
    return ENFA(a.k, a.n + b.n, a.starts,
                frozenset(q + off for q in b.finals), frozenset(edges))


def star(m):
    a = as_enfa(m)
    z = a.n
    edges = set(a.edges) | {(z, None, q) for q in a.starts}
    edges |= {(q, None, z) for q in a.finals}
    return ENFA(a.k, a.n + 1, frozenset([z]), frozenset([z]), frozenset(edges))


ZERO, ONE = ("zero",), ("one",)
def letter(a): return ("letter", a)
def alt(a, b): return ("alt", a, b)
def seq(a, b): return ("seq", a, b)
def repeat(a): return ("star", a)


def regex_accepts(expr, word):
    """Direct interval semantics, independent of automata constructions."""
    @lru_cache(None)
    def member(e, i, j):
        tag = e[0]
        if tag == "zero": return False
        if tag == "one": return i == j
        if tag == "letter": return j == i + 1 and word[i] == e[1]
        if tag == "alt": return member(e[1], i, j) or member(e[2], i, j)
        if tag == "seq":
            return any(member(e[1], i, t) and member(e[2], t, j)
                       for t in range(i, j + 1))
        if tag == "star":
            reachable = {i}
            for t in range(i + 1, j + 1):
                if any(member(e[1], s, t) for s in range(i, t) if s in reachable):
                    reachable.add(t)
            return j in reachable
        raise ValueError(tag)
    return member(expr, 0, len(word))


def thompson(expr, k):
    edges = set()
    count = 0
    def build(e):
        nonlocal count
        entry, exit = count, count + 1
        count += 2
        tag = e[0]
        if tag == "zero": pass
        elif tag == "one": edges.add((entry, None, exit))
        elif tag == "letter": edges.add((entry, e[1], exit))
        elif tag in ("alt", "seq"):
            ae, ax = build(e[1]); be, bx = build(e[2])
            if tag == "alt":
                edges.update(((entry, None, ae), (entry, None, be),
                              (ax, None, exit), (bx, None, exit)))
            else:
                edges.update(((entry, None, ae), (ax, None, be), (bx, None, exit)))
        elif tag == "star":
            ae, ax = build(e[1])
            edges.update(((entry, None, exit), (entry, None, ae),
                          (ax, None, ae), (ax, None, exit)))
        else: raise ValueError(tag)
        return entry, exit
    entry, exit = build(expr)
    return ENFA(k, count, frozenset([entry]), frozenset([exit]), frozenset(edges))


def eliminate(m):
    """Exact Kleene recurrence; tuples share repeated subexpressions."""
    rows = [[ONE if i == j else ZERO for j in range(m.n)] for i in range(m.n)]
    for i in range(m.n):
        for a in range(m.k):
            j = m.table[i][a]
            rows[i][j] = alt(rows[i][j], letter(a))
    for h in range(m.n):
        old = rows
        rows = [[alt(old[i][j], seq(seq(old[i][h], repeat(old[h][h])), old[h][j]))
                 for j in range(m.n)] for i in range(m.n)]
    out = ZERO
    for q in sorted(m.finals):
        out = alt(out, rows[m.start][q])
    return out


def access_words(m):
    found = {m.start: ()}
    todo = deque([m.start])
    while todo:
        q = todo.popleft()
        for a in range(m.k):
            r = m.table[q][a]
            if r not in found:
                found[r] = found[q] + (a,)
                todo.append(r)
    return found


def shortest_separator(a, b):
    p = combine(a, b, lambda x, y: x != y)
    access = access_words(p)
    witnesses = [w for q, w in access.items() if q in p.finals]
    return min(witnesses, key=lambda w: (len(w), w)) if witnesses else None


def distinguishers(m):
    """Return a suffix or None for every pair, after exactly n^2 rounds."""
    d = [[() if ((q in m.finals) != (r in m.finals)) else None
          for r in range(m.n)] for q in range(m.n)]
    for _ in range(m.n * m.n):
        nxt = [row[:] for row in d]
        for q in range(m.n):
            for r in range(m.n):
                if d[q][r] is None:
                    for a in range(m.k):
                        tail = d[m.table[q][a]][m.table[r][a]]
                        if tail is not None:
                            nxt[q][r] = (a,) + tail
                            break
        d = nxt
    return d


def minimize(m):
    access = access_words(m)
    reachable = sorted(access)
    d = distinguishers(m)
    representative = {q: min(r for r in reachable if d[q][r] is None)
                      for q in reachable}
    reps = sorted(set(representative.values()))
    numbering = {q: i for i, q in enumerate(reps)}
    index = lambda q: numbering[representative[q]]
    result = DFA(m.k,
                 tuple(tuple(index(m.table[q][a]) for a in range(m.k)) for q in reps),
                 index(m.start), frozenset(index(q) for q in reps if q in m.finals))
    return result.validate(), tuple(access[q] for q in reps), d


def words(k, upper):
    for n in range(upper + 1):
        yield from product(range(k), repeat=n)


def finiteness_certificate(m):
    for w in words(m.k, 2 * m.n - 1):
        if len(w) >= m.n and m.accepts(w):
            return "infinite", w
    return "finite", tuple(w for w in words(m.k, m.n - 1) if m.accepts(w))


def direct_star_accepts(m, w):
    good = [True] + [False] * len(w)
    for j in range(1, len(w) + 1):
        good[j] = any(good[i] and m.accepts(w[i:j]) for i in range(j))
    return good[-1]


def self_check():
    statistics = {"dfa_models": 0, "word_comparisons": 0,
                  "epsilon_models": 0, "pair_comparisons": 0}
    automata = []
    # Exhaust every binary 2-state transition table and accepting set, start 0.
    for raw in product(range(2), repeat=4):
        table = (raw[:2], raw[2:])
        for mask in range(4):
            m = DFA(2, table, 0, frozenset(q for q in range(2) if mask >> q & 1)).validate()
            automata.append(m)
            statistics["dfa_models"] += 1
            e = eliminate(m)
            rev = determinize(reverse(m))
            st = determinize(star(m))
            minimized, access, d = minimize(m)
            assert shortest_separator(m, minimized) is None
            assert all(len(w) < m.n for w in access)
            if minimized.n == 2:
                for bit in range(2):
                    constant = DFA(2, ((0, 0),), 0, frozenset([0]) if bit else frozenset())
                    assert shortest_separator(m, constant) is not None
            for w in words(2, 6):
                expected = m.accepts(w)
                assert regex_accepts(e, w) == expected
                assert minimized.accepts(w) == expected
                assert rev.accepts(w) == m.accepts(w[::-1])
                assert st.accepts(w) == direct_star_accepts(m, w)
                statistics["word_comparisons"] += 4
            status, certificate = finiteness_certificate(m)
            if status == "finite":
                assert all(not m.accepts(w) or w in certificate for w in words(2, 8))
            else:
                assert 2 <= len(certificate) < 4 and m.accepts(certificate)
    # Every pair's BFS separator is compared with independent bounded enumeration.
    for a in automata:
        for b in automata:
            witness = shortest_separator(a, b)
            reference = next((w for w in words(2, 3) if a.accepts(w) != b.accepts(w)), None)
            assert witness == reference
            statistics["pair_comparisons"] += 1
    # Every pair of unary edge/epsilon relations on two states (256 machines).
    arcs = tuple(product(range(2), repeat=2))
    for ordinary in range(16):
        for empty in range(16):
            edges = {(q, 0, r) for j, (q, r) in enumerate(arcs) if ordinary >> j & 1}
            edges |= {(q, None, r) for j, (q, r) in enumerate(arcs) if empty >> j & 1}
            m = ENFA(1, 2, frozenset([0]), frozenset([1]), frozenset(edges))
            det = determinize(m)
            for w in words(1, 8):
                assert det.accepts(w) == m.accepts_graph(w)
                statistics["word_comparisons"] += 1
            statistics["epsilon_models"] += 1
    # Thompson graphs independently checked against direct interval semantics,
    # including epsilon-containing stars and nested stars.
    expressions = [ZERO, ONE, letter(0), alt(ONE, letter(1)),
                   seq(repeat(letter(0)), letter(1)),
                   repeat(alt(ONE, seq(letter(0), letter(1)))),
                   repeat(repeat(alt(letter(0), letter(1))))]
    for e in expressions:
        nfa = thompson(e, 2)
        for w in words(2, 6):
            assert nfa.accepts_graph(w) == regex_accepts(e, w)
            statistics["word_comparisons"] += 1
    # Concatenation checked against all possible input cuts.
    for a, b in zip(automata[::8], automata[7::8]):
        machine = concatenate(a, b)
        for w in words(2, 6):
            expected = any(a.accepts(w[:i]) and b.accepts(w[i:]) for i in range(len(w)+1))
            assert machine.accepts_graph(w) == expected
            statistics["word_comparisons"] += 1
    statistics["status"] = "all checks passed"
    return statistics


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2, sort_keys=True))
