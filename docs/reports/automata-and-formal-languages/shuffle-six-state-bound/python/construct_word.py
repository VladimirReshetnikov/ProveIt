#!/usr/bin/env python3
"""Construct access words using the proved reductions and supplied certificates.

Input example: python python/construct_word.py --rows 6 \
    --columns 12,17,18,24,33,34,36 --output example.json
Column masks describe the target; a letter is a pair of complete transformations.
The program always checks its output by forward simulation.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
Cell = tuple[int, int]
Letter = tuple[list[int], list[int]]


def step(states: set[Cell], letter: Letter) -> set[Cell]:
    f, g = letter
    return {(f[i], j) for i, j in states} | {(i, g[j]) for i, j in states}


def valid(states: set[Cell], start: Cell) -> bool:
    return any(i == start[0] for i, j in states) and any(j == start[1] for i, j in states)


class Constructor:
    def __init__(self, path: Path = ROOT/'certificates/cores.cert') -> None:
        self.certificates = {}
        for line in path.read_text().splitlines():
            if not line or line.startswith('#'):
                continue
            v = list(map(int, line.split()))
            m, n, family = v[:3]
            if len(v) != 3+m+2*n:
                raise ValueError('Malformed certificate record')
            self.certificates[m, family] = (v[3:3+m], v[3+m:3+m+n], v[3+m+n:])

    @staticmethod
    def lift(word: list[Letter], rows: list[int], cols: list[int],
             m: int, n: int) -> list[Letter]:
        result = []
        for f, g in word:
            F, G = list(range(m)), list(range(n))
            for i, r in enumerate(rows):
                F[r] = rows[f[i]]
            for j, c in enumerate(cols):
                G[c] = cols[g[j]]
            result.append((F, G))
        return result

    def construct(self, m: int, n: int, states: set[Cell],
                  start: Cell = (0, 0)) -> list[Letter]:
        if (m < 1 or n < 1 or min(m, n) > 6 or not (0 <= start[0] < m)
                or not (0 <= start[1] < n)
                or any(not (0 <= i < m and 0 <= j < n) for i, j in states)
                or not valid(states, start)):
            raise ValueError('Need a valid subset of a positive grid with min(m,n)<=6')
        word = self._construct(m, n, states, start)
        reached = {start}
        for letter in word:
            reached = step(reached, letter)
        if reached != states or len(word) > len(states)+min(m, n)-2:
            raise RuntimeError('Constructed word failed independent forward check')
        return word

    def _construct(self, m: int, n: int, S: set[Cell], start: Cell) -> list[Letter]:
        if m > n:
            return [(g, f) for f, g in self._construct(
                n, m, {(j, i) for i, j in S}, (start[1], start[0]))]
        if m == 1:
            word = []
            for j in sorted({j for i, j in S} - {start[1]}):
                g = list(range(n)); g[start[1]] = j
                word.append(([0], g))
            return word
        rows = sorted({i for i, j in S}); cols = sorted({j for i, j in S})
        if len(rows) < m or len(cols) < n:
            ri = {r: i for i, r in enumerate(rows)}
            cj = {c: j for j, c in enumerate(cols)}
            word = self._construct(len(rows), len(cols),
                                   {(ri[i], cj[j]) for i, j in S},
                                   (ri[start[0]], cj[start[1]]))
            return self.lift(word, rows, cols, m, n)
        R = [{j for r, j in S if r == i} for i in range(m)]
        C = [{i for i, c in S if c == j} for j in range(n)]
        for i in range(m):
            for j in range(m):
                if i != j and R[i] <= R[j]:
                    T = S - {(j, c) for c in R[i]}
                    if valid(T, start):
                        f = list(range(m)); f[i] = j
                        return self._construct(m, n, T, start) + [(f, list(range(n)))]
        for i in range(n):
            for j in range(n):
                if i != j and C[i] <= C[j]:
                    T = S - {(r, j) for r in C[i]}
                    if valid(T, start):
                        g = list(range(n)); g[i] = j
                        return self._construct(m, n, T, start) + [(list(range(m)), g)]
        isolated = [(i, j) for i, j in S if len(R[i]) == len(C[j]) == 1]
        if isolated:
            p, q = min(isolated)
            rows = [i for i in range(m) if i != p]
            cols = [j for j in range(n) if j != q]
            r = start[0] if start[0] != p else rows[0]
            c = start[1] if start[1] != q else cols[0]
            f, g = list(range(m)), list(range(n))
            f[p], f[r] = r, p; g[q], g[c] = c, q
            repeats = 1 if ((p == start[0]) != (q == start[1])) else 2
            seed = [(f, g)] * repeats
            ri = {x: k for k, x in enumerate(rows)}
            cj = {x: k for k, x in enumerate(cols)}
            word = self._construct(m-1, n-1,
                {(ri[i], cj[j]) for i, j in S if (i, j) != (p, q)}, (ri[r], cj[c]))
            return seed + self.lift(word, rows, cols, m, n)
        # An irreducible core: canonicalize by sorted row degrees, then family.
        degrees = [len(r) for r in R]; ordered_degrees = sorted(degrees)
        column_masks = [sum(1 << i for i in C[j]) for j in range(n)]
        best = None
        for p in itertools.permutations(range(m)):
            if any(degrees[i] != ordered_degrees[p[i]] for i in range(m)):
                continue
            transformed = [sum(1 << p[i] for i in range(m) if (mask >> i) & 1)
                           for mask in column_masks]
            family = sum(1 << mask for mask in transformed)
            if best is None or family < best[0]:
                best = (family, p, transformed)
        if best is None:
            raise RuntimeError('No canonical representative')
        family, p, transformed = best
        f, g, masks = self.certificates[m, family]
        sorted_columns = sorted(transformed)
        q = [sorted_columns.index(mask) for mask in transformed]
        ip = [p.index(i) for i in range(m)]
        iq = [q.index(j) for j in range(n)]
        T = {(ip[i], iq[j]) for j, mask in enumerate(masks)
             for i in range(m) if (mask >> i) & 1}
        F = [ip[f[p[i]]] for i in range(m)]
        G = [iq[g[q[j]]] for j in range(n)]
        if len(T) >= len(S) or not valid(T, start) or step(T, (F, G)) != S:
            raise RuntimeError('Invalid transported certificate')
        return self._construct(m, n, T, start) + [(F, G)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows', type=int, required=True)
    parser.add_argument('--columns', required=True, help='Comma-separated column bit masks')
    parser.add_argument('--start', default='0,0', help='Initial row,column')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    columns = [int(x) for x in args.columns.split(',')]
    start = tuple(map(int, args.start.split(',')))
    if len(start) != 2 or not columns or any(c < 0 or c >= 1 << args.rows for c in columns):
        parser.error('Invalid columns or start')
    S = {(i, j) for j, c in enumerate(columns) for i in range(args.rows) if (c >> i) & 1}
    word = Constructor().construct(args.rows, len(columns), S, start)
    out = {'rows': args.rows, 'columns': len(columns), 'start': list(start),
           'target_columns': columns, 'target_cells': len(S), 'word_length': len(word),
           'length_bound': len(S)+min(args.rows, len(columns))-2,
           'word': [{'f': f, 'g': g} for f, g in word]}
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(f'Forward-verified {len(word)}-letter access word written to {args.output}')


if __name__ == '__main__':
    main()
