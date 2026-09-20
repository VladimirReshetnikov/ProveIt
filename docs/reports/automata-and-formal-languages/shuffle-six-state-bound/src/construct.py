#!/usr/bin/env python3
"""Construct and replay a word reaching a valid shuffle subset (min(m,n)<=6).

The algorithm implements the induction in the article.  It never calls a solver.
The supplied certificate file must first pass both independent audit programs.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import permutations
import argparse
import json
from pathlib import Path
from typing import Iterable
from check_certificates import require, check_record

Cell = tuple[int, int]
State = frozenset[Cell]
Letter = tuple[tuple[int, ...], tuple[int, ...]]
Word = list[Letter]


def transition(state: Iterable[Cell], letter: Letter) -> State:
    f, g = letter
    source = tuple(state)
    return frozenset([(f[i], j) for i, j in source]
                     + [(i, g[j]) for i, j in source])


def replay(m: int, n: int, word: Word, root: Cell = (0, 0)) -> State:
    state = frozenset([root])
    for f, g in word:
        require(len(f) == m and len(g) == n, "letter has wrong dimensions")
        require(all(0 <= i < m for i in f) and all(0 <= j < n for j in g),
                "letter image outside state space")
        state = transition(state, (f, g))
    return state


def lift(word: Word, rows: list[int], columns: list[int], m: int, n: int) -> Word:
    """Extend a word on the indicated subgrid, fixing every excluded coordinate."""
    result = []
    for f0, g0 in word:
        f, g = list(range(m)), list(range(n))
        for i, old in enumerate(rows):
            f[old] = rows[f0[i]]
        for j, old in enumerate(columns):
            g[old] = columns[g0[j]]
        result.append((tuple(f), tuple(g)))
    return result


@dataclass
class Constructor:
    certificates: dict[tuple[int, int], dict]

    @classmethod
    def load(cls, path: Path) -> Constructor:
        certificates = {}
        for line in path.read_text().splitlines():
            rec = json.loads(line)
            check_record(rec)
            key = (rec["m"], rec["family"])
            require(key not in certificates, "duplicate certificate")
            certificates[key] = rec
        return cls(certificates)

    def predecessor(self, m: int, n: int, S: State) -> tuple[State, Letter]:
        """Transport an unrooted spanning certificate by explicit permutations."""
        cols = [sum(1 << i for i in range(m) if (i, j) in S) for j in range(n)]
        require(len(set(cols)) == n, "hard target has repeated columns")
        for p in permutations(range(m)):
            renamed = [sum(1 << p[i] for i in range(m) if s & (1 << i)) for s in cols]
            family = sum(1 << s for s in renamed)
            rec = self.certificates.get((m, family))
            if rec is None:
                continue
            index = {s: j for j, s in enumerate(rec["columns"])}
            q = [index[s] for s in renamed]
            pinv = [p.index(i) for i in range(m)]
            qinv = [q.index(j) for j in range(n)]
            T = frozenset((pinv[i], qinv[j]) for i, j in rec["T"])
            f = tuple(pinv[rec["f"][p[i]]] for i in range(m))
            g = tuple(qinv[rec["g"][q[j]]] for j in range(n))
            require(transition(T, (f, g)) == S and len(T) < len(S),
                    "transported predecessor failed validation")
            return T, (f, g)
        raise ValueError(f"no certificate representative for {m}x{n} target")

    def reach(self, m: int, n: int, state: Iterable[Cell], root: Cell = (0, 0)) -> Word:
        S = frozenset(state)
        r, c = root
        require(m >= 1 and n >= 1 and min(m, n) <= 6, "unsupported dimensions")
        require(0 <= r < m and 0 <= c < n, "root outside grid")
        require(all(0 <= i < m and 0 <= j < n for i, j in S), "cell outside grid")
        require(any(i == r for i, j in S) and any(j == c for i, j in S), "invalid target")
        word = self._reach(m, n, S, root)
        require(replay(m, n, word, root) == S, "constructed word failed replay")
        require(len(word) <= len(S) + min(m, n) - 2, "length bound violated")
        return word

    def _reach(self, m: int, n: int, S: State, root: Cell) -> Word:
        r, c = root
        if m > 6:
            transposed = frozenset((j, i) for i, j in S)
            return [(g, f) for f, g in self._reach(n, m, transposed, (c, r))]
        if m == 1:
            word = []
            for j in sorted(j for i, j in S if j != c):
                g = list(range(n)); g[c] = j
                word.append(((0,), tuple(g)))
            return word
        if n == 1:
            word = []
            for i in sorted(i for i, j in S if i != r):
                f = list(range(m)); f[r] = i
                word.append((tuple(f), (0,)))
            return word
        rowsets = [{j for x, j in S if x == i} for i in range(m)]
        colsets = [{i for i, y in S if y == j} for j in range(n)]
        rows = [i for i in range(m) if rowsets[i]]
        cols = [j for j in range(n) if colsets[j]]
        if len(rows) < m or len(cols) < n:
            ri = {i: k for k, i in enumerate(rows)}
            ci = {j: k for k, j in enumerate(cols)}
            compressed = frozenset((ri[i], ci[j]) for i, j in S)
            subword = self._reach(len(rows), len(cols), compressed, (ri[r], ci[c]))
            return lift(subword, rows, cols, m, n)
        # Delete a duplicate copy from the containing row. In the equality case,
        # never choose the distinguished row as the containing destination.
        for i in range(m):
            for k in range(m):
                if i != k and rowsets[i] <= rowsets[k]:
                    if rowsets[i] == rowsets[k] and k == r:
                        continue
                    T = S - frozenset((k, j) for j in rowsets[i])
                    f = list(range(m)); f[i] = k
                    return self._reach(m, n, T, root) + [(tuple(f), tuple(range(n)))]
        for j in range(n):
            for k in range(n):
                if j != k and colsets[j] <= colsets[k]:
                    if colsets[j] == colsets[k] and k == c:
                        continue
                    T = S - frozenset((i, k) for i in colsets[j])
                    g = list(range(n)); g[j] = k
                    return self._reach(m, n, T, root) + [(tuple(range(m)), tuple(g))]
        isolated = next(((i, j) for i, j in sorted(S)
                         if len(rowsets[i]) == 1 or len(colsets[j]) == 1), None)
        if isolated is not None:
            p, q = isolated
            require(len(rowsets[p]) == len(colsets[q]) == 1, "edge is not isolated")
            r2 = r if r != p else next(i for i in range(m) if i != p)
            c2 = c if c != q else next(j for j in range(n) if j != q)
            rows = [i for i in range(m) if i != p]
            cols = [j for j in range(n) if j != q]
            ri = {i: k for k, i in enumerate(rows)}
            ci = {j: k for k, j in enumerate(cols)}
            small = frozenset((ri[i], ci[j]) for i, j in S if (i, j) != (p, q))
            subword = self._reach(m-1, n-1, small, (ri[r2], ci[c2]))
            f, g = list(range(m)), list(range(n))
            f[p], f[r2] = r2, p
            g[q], g[c2] = c2, q
            a = (tuple(f), tuple(g))
            seed_word = [a] * (2 if (r == p) == (c == q) else 1)
            require(replay(m, n, seed_word, root) == frozenset([(p, q), (r2, c2)]),
                    "isolated-edge seed failed")
            return seed_word + lift(subword, rows, cols, m, n)
        T, a = self.predecessor(m, n, S)
        return self._reach(m, n, T, root) + [a]


def main() -> int:
    package = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON with m,n,target (cell list), optional root")
    parser.add_argument("--certificates", type=Path, default=package / "data/certificates.jsonl")
    parser.add_argument("--output", type=Path, help="output JSON; otherwise print to stdout")
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    constructor = Constructor.load(args.certificates)
    root = tuple(data.get("root", [0, 0]))
    word = constructor.reach(data["m"], data["n"], data["target"], root)
    result = dict(data, word=[{"f": f, "g": g} for f, g in word], word_length=len(word),
                  length_bound=len(set(map(tuple, data["target"]))) + min(data["m"], data["n"]) - 2,
                  replay="PASS")
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
