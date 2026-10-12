"""Validated finite occurrence data. No geometric trust is inferred here."""
from dataclasses import dataclass
from typing import Callable

Check = Callable[[], None]
def noop() -> None:
    pass

@dataclass
class Matrix:
    rows: tuple[int, ...]
    cols: tuple[int, ...]
    entries: dict[int, dict[int, int]]
    weights: dict[int, int]

    @classmethod
    def parse(cls, counts: dict, weights: dict | None = None) -> 'Matrix':
        if type(counts) is not dict:
            raise ValueError('counts must be a dictionary of occurrence rows')
        entries = {}
        for r, row in counts.items():
            if type(r) is not int or r < 0 or type(row) is not dict:
                raise ValueError('row labels must be nonnegative integers')
            entries[r] = {}
            for c, a in row.items():
                if type(c) is not int or c < 0 or type(a) is not int or a < 0:
                    raise ValueError('invalid nonnegative integral occurrence')
                if a:
                    entries[r][c] = a
        rows = tuple(sorted(entries))
        cols = tuple(sorted({c for row in entries.values() for c in row}))
        if weights is None:
            weights = {r: 1 for r in rows}
        if (type(weights) is not dict or set(weights) != set(rows)
                or any(type(w) is not int or w < 0 for w in weights.values())):
            raise ValueError('weights must assign each row a nonnegative integer')
        return cls(rows, cols, entries, dict(weights))

    def graph(self):
        # Graph indices are dense and local, never confused with source labels.
        pivot_cols = {c for row in self.entries.values() for c, a in row.items() if a == 1}
        labels = tuple(('r', r) for r in self.rows) + tuple(('c', c) for c in self.cols if c in pivot_cols)
        inv = {v: i for i, v in enumerate(labels)}
        adj = [set() for _ in labels]
        edges = []
        for r in self.rows:
            for c, a in sorted(self.entries[r].items()):
                if c not in pivot_cols:
                    continue
                u, v = inv['r', r], inv['c', c]
                adj[u].add(v); adj[v].add(u)
                edges.append((u, v, a == 1))
        return labels, adj, edges
