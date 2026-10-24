"""Small exact arithmetic-circuit emitter (Python standard library)."""
from collections import Counter


class Graph:
    def __init__(self, variables):
        self.variables = list(variables)
        self.nodes, self.cache = [], {}

    def intern(self, node):
        node = tuple(node)
        if node not in self.cache:
            self.cache[node] = len(self.nodes)
            self.nodes.append(list(node))
        return Expr(self, self.cache[node])

    def coerce(self, value):
        if isinstance(value, Expr):
            if value.graph is not self:
                raise ValueError('foreign graph')
            return value
        if not isinstance(value, int):
            raise TypeError('only integer literals are allowed')
        return self.intern(('integer', value))

    def op(self, op, x, y):
        x, y = self.coerce(x), self.coerce(y)
        a, b = self.nodes[x.index], self.nodes[y.index]
        if a[0] == b[0] == 'integer':
            return self.coerce({'add': lambda: a[1]+b[1],
                                'sub': lambda: a[1]-b[1],
                                'mul': lambda: a[1]*b[1]}[op]())
        if op == 'mul':
            if a == ['integer', 0] or b == ['integer', 0]: return self.coerce(0)
            if a == ['integer', 1]: return y
            if b == ['integer', 1]: return x
        if op == 'add':
            if a == ['integer', 0]: return y
            if b == ['integer', 0]: return x
        if op == 'sub':
            if b == ['integer', 0]: return x
            if x.index == y.index: return self.coerce(0)
        if op in ('add', 'mul') and x.index > y.index:
            x, y = y, x
        return self.intern((op, x.index, y.index))

    def export(self, name, output, registers):
        live = set()
        def visit(i):
            if i in live: return
            live.add(i)
            row = self.nodes[i]
            if row[0] in ('add', 'sub', 'mul'):
                visit(row[1]); visit(row[2])
        visit(output.index)
        order = sorted(live)
        remap = {old: new for new, old in enumerate(order)}
        nodes = []
        for old in order:
            row = self.nodes[old]
            nodes.append([row[0], remap[row[1]], remap[row[2]]]
                         if row[0] in ('add', 'sub', 'mul') else list(row))
        counts = Counter(r[0] for r in nodes if r[0] in ('add', 'sub', 'mul'))
        used = {r[1] for r in nodes if r[0] == 'variable'}
        if used != set(self.variables): raise ValueError('dead or missing variable')
        return dict(schema='integer-polynomial-dag-v1', name=name,
                    domain='unrestricted integers', variables=self.variables,
                    variable_count=len(used), nodes=nodes, output=remap[output.index],
                    named_registers={k:remap[v.index] for k,v in registers.items()
                                     if isinstance(v,Expr) and v.index in live},
                    operation_counts=dict(sorted(counts.items())),
                    operations=sum(counts.values()),
                    coefficient_binding='coefficients/BINDING.json')


class Expr:
    def __init__(self, graph, index): self.graph, self.index = graph, index
    def __add__(self, other): return self.graph.op('add', self, other)
    def __radd__(self, other): return self.graph.op('add', other, self)
    def __sub__(self, other): return self.graph.op('sub', self, other)
    def __rsub__(self, other): return self.graph.op('sub', other, self)
    def __mul__(self, other): return self.graph.op('mul', self, other)
    def __rmul__(self, other): return self.graph.op('mul', other, self)
    def __pow__(self, power):
        if not isinstance(power, int) or power < 0: raise ValueError('fixed exponent required')
        if power == 0: return self.graph.coerce(1)
        if power == 1: return self
        half = self ** (power//2)
        return half*half if power % 2 == 0 else half*half*self
