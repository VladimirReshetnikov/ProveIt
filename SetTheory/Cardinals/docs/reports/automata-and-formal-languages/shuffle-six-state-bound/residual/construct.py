#!/usr/bin/env python3
"""Construct a reaching word for any valid grid with min(m,n) <= 6.

Examples:
  python construct.py --rows 6 --columns 7 --masks 3,5,9,14,17,33,50
  python construct.py --rows 3 --columns 3 --masks 1,2,4
Column masks use bit i for row i. All indices are zero-based. The output is JSON:
each letter contains the two complete state transformations f and g. No enormous
alphabet is explicitly materialized. Python 3.9+, standard library only.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from typing import Iterable, List, Set, Tuple
from verify import (balanced_triple, cells, image, load_certificates,
                    orbit_tables, require)

Cell = Tuple[int, int]
Letter = Tuple[Tuple[int, ...], Tuple[int, ...]]
Word = List[Letter]


class Constructor:
    def __init__(self, certificate_path: Path = Path(__file__).with_name("certificates.tsv")):
        self.records = load_certificates(certificate_path)
        self.tables = orbit_tables(self.records)

    @staticmethod
    def replay(origin: Cell, word: Iterable[Letter]) -> Set[Cell]:
        state = {origin}
        for f, g in word:
            state = image(state, f, g)
        return state

    @staticmethod
    def _lift(word: Word, rows: List[int], cols: List[int], m: int, n: int) -> Word:
        lifted = []
        for f, g in word:
            F, G = list(range(m)), list(range(n))
            for i, old in enumerate(rows):
                F[old] = rows[f[i]]
            for j, old in enumerate(cols):
                G[old] = cols[g[j]]
            lifted.append((tuple(F), tuple(G)))
        return lifted

    def _restricted(self, m: int, n: int, S: Set[Cell], origin: Cell,
                    rows: List[int], cols: List[int]) -> Word:
        ri = {old: new for new, old in enumerate(rows)}
        ci = {old: new for new, old in enumerate(cols)}
        reduced = {(ri[i], ci[j]) for i, j in S}
        word = self._reach(len(rows), len(cols), reduced,
                           (ri[origin[0]], ci[origin[1]]))
        return self._lift(word, rows, cols, m, n)

    def _reach(self, m: int, n: int, S: Set[Cell], origin: Cell) -> Word:
        r0, c0 = origin
        if S == {origin}:
            return []
        if m > n:
            word = self._reach(n, m, {(j, i) for i, j in S}, (c0, r0))
            return [(g, f) for f, g in word]
        rows = [{j for i, j in S if i == r} for r in range(m)]
        cols = [{i for i, j in S if j == c} for c in range(n)]
        for r in range(m):
            if not rows[r]:
                return self._restricted(m, n, S, origin,
                                        [i for i in range(m) if i != r], list(range(n)))
        for c in range(n):
            if not cols[c]:
                return self._restricted(m, n, S, origin,
                                        list(range(m)), [j for j in range(n) if j != c])
        for a in range(m):
            for b in range(m):
                if a != b and rows[a] <= rows[b] and (b != r0 or rows[b] - rows[a]):
                    T = S - {(b, j) for j in rows[a]}
                    f = list(range(m)); f[a] = b
                    return self._reach(m, n, T, origin) + [(tuple(f), tuple(range(n)))]
        for a in range(n):
            for b in range(n):
                if a != b and cols[a] <= cols[b] and (b != c0 or cols[b] - cols[a]):
                    T = S - {(i, b) for i in cols[a]}
                    g = list(range(n)); g[a] = b
                    return self._reach(m, n, T, origin) + [(tuple(range(m)), tuple(g))]
        # With incomparable, nonempty neighborhoods, any degree-one vertex
        # belongs to an isolated edge.
        for p in range(m):
            if len(rows[p]) == 1:
                q = next(iter(rows[p]))
                require(cols[q] == {p}, "isolated-edge invariant")
                r = r0 if r0 != p else next(i for i in range(m) if i != p)
                c = c0 if c0 != q else next(j for j in range(n) if j != q)
                f, g = list(range(m)), list(range(n))
                f[p], f[r] = f[r], f[p]
                g[q], g[c] = g[c], g[q]
                exponent = 2 if (r0 == p) == (c0 == q) else 1
                remaining = self._restricted(
                    m, n, S - {(p, q)}, (r, c),
                    [i for i in range(m) if i != p],
                    [j for j in range(n) if j != q])
                return [(tuple(f), tuple(g))] * exponent + remaining
        masks = tuple(sum(1 << i for i in col) for col in cols)
        triple = balanced_triple(masks)
        if triple is not None:
            a, b, c = triple
            g = list(range(n)); g[a], g[b], g[c] = b, c, a
            pre = list(masks)
            pre[a], pre[b], pre[c] = masks[a] & masks[b], masks[b] & masks[c], masks[c] & masks[a]
            T = cells(pre, m)
            return self._reach(m, n, T, origin) + [(tuple(range(m)), tuple(g))]
        key = tuple(sorted(masks))
        require(m in self.tables and key in self.tables[m], f"missing certificate: {m}x{n} {key}")
        index, p = self.tables[m][key]
        record = self.records[index]
        actual_col = {mask: j for j, mask in enumerate(masks)}
        c = tuple(actual_col[sum(1 << p[i] for i in range(m) if mask & (1 << i))]
                  for mask in record["columns"])
        T = {(p[i], c[j]) for i, j in cells(record["predecessor"], m)}
        f, g = [0] * m, [0] * n
        for i in range(m):
            f[p[i]] = p[record["f"][i]]
        for j in range(n):
            g[c[j]] = c[record["g"][j]]
        require(image(T, tuple(f), tuple(g)) == S, "transported certificate")
        return self._reach(m, n, T, origin) + [(tuple(f), tuple(g))]

    def reach(self, m: int, n: int, target: Iterable[Cell], origin: Cell = (0, 0)) -> Word:
        require(m >= 1 and n >= 1 and min(m, n) <= 6, "require positive dimensions and min(m,n)<=6")
        require(0 <= origin[0] < m and 0 <= origin[1] < n, "origin outside grid")
        S = set(target)
        require(all(0 <= i < m and 0 <= j < n for i, j in S), "target outside grid")
        require(any(i == origin[0] for i, _ in S) and any(j == origin[1] for _, j in S),
                "target must meet the initial row and initial column")
        # The inductive construction has depth O(|S|+m+n); this implementation
        # uses the Python stack rather than claiming an unbounded stack size.
        sys.setrecursionlimit(max(sys.getrecursionlimit(), 4 * (len(S) + m + n) + 100))
        word = self._reach(m, n, S, origin)
        require(self.replay(origin, word) == S, "final word replay failed")
        bound = min(2 * (len(S) - 1), len(S) + min(m, n) - 2)
        require(len(word) <= bound, "length bound failed")
        return word


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int, required=True)
    parser.add_argument("--columns", type=int, required=True)
    parser.add_argument("--masks", required=True, help="comma-separated column masks")
    parser.add_argument("--origin", default="0,0")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    masks = tuple(map(int, args.masks.split(",")))
    origin = tuple(map(int, args.origin.split(",")))
    require(len(masks) == args.columns, "number of masks")
    require(len(origin) == 2, "origin must have two coordinates")
    require(all(0 <= x < (1 << args.rows) for x in masks), "column-mask range")
    target = cells(masks, args.rows)
    word = Constructor().reach(args.rows, args.columns, target, origin)
    result = {"rows": args.rows, "columns": args.columns,
              "origin": origin, "target_column_masks": masks,
              "target_size": len(target), "word_length": len(word),
              "word": [{"f": f, "g": g} for f, g in word], "replay_verified": True}
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")

if __name__ == "__main__":
    main()
