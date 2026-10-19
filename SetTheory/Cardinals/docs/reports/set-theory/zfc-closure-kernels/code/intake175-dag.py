"""Source-DAG utilities: intern a sites list into a hash-consed DAG of distinct subtrees."""
import json


def load_sites(path):
    return json.load(open(path, encoding="utf-8"))


class DAG:
    def __init__(self, sites):
        self.leaf = {p: (k, a) for p, k, a in sites}
        self.ids, self.struct, self.pathnode = {}, [], {}
        self.root = self.intern("")

    def intern(self, p):
        if p in self.leaf:
            key = self.leaf[p]
        else:
            key = (self.intern(p + "0"), self.intern(p + "1"))
        if key not in self.ids:
            self.ids[key] = len(self.struct)
            self.struct.append(key)
        n = self.ids[key]
        self.pathnode[p] = n
        return n

    def is_leaf(self, n):
        return isinstance(self.struct[n][0], str)

    def interior(self):
        return [n for n in range(len(self.struct)) if not self.is_leaf(n)]

    def shape(self, n):
        x = self.struct[n]
        return f"{x[0]}:{x[1]}" if isinstance(x[0], str) else f"({self.shape(x[0])},{self.shape(x[1])})"

    def nleaves(self, n):
        x = self.struct[n]
        return 1 if isinstance(x[0], str) else self.nleaves(x[0]) + self.nleaves(x[1])

    def stats(self):
        return dict(distinct=len(self.struct), interior=len(self.interior()),
                    leaf_kinds=len(self.struct) - len(self.interior()),
                    leaves=len(self.leaf), depth=max(map(len, self.leaf)),
                    max_zero_run=max(max((len(r) for r in p.split("1")), default=0) for p in self.leaf))
