#!/usr/bin/env python3
"""Literal division-free consistency polynomials. Python standard library only.

The generated DAGs contain only integer numeral/variable leaves and binary
addition, subtraction, multiplication. No proof search is run.
"""
from pathlib import Path
from collections import Counter
import gzip, hashlib, importlib.util, json
from five_square_norm import cleared_norm5

ROOT = Path(__file__).resolve().parent
BASE_PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
VARS12 = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 'p2', 'p3']

def require(ok, message):
    if not ok:
        raise ValueError(message)

class DAG:
    def __init__(self, variables):
        self.nodes = []
        self.index = {}
        self.variables = list(variables)
    def leaf(self, kind, value):
        return self.intern((kind, value))
    def intern(self, key):
        if key not in self.index:
            self.index[key] = len(self.nodes)
            self.nodes.append(list(key))
        return Expr(self, self.index[key])
    def coerce(self, value):
        if isinstance(value, Expr):
            require(value.d is self, 'foreign arithmetic register')
            return value
        require(isinstance(value, int), 'integer literal required')
        return self.leaf('integer', value)
    def op(self, tag, left, right):
        a, b = self.coerce(left), self.coerce(right)
        na, nb = self.nodes[a.i], self.nodes[b.i]
        if na[0] == nb[0] == 'integer':
            x, y = na[1], nb[1]
            return self.coerce(x+y if tag == 'add' else x-y if tag == 'sub' else x*y)
        if tag == 'mul':
            if na == ['integer', 0] or nb == ['integer', 0]: return self.coerce(0)
            if na == ['integer', 1]: return b
            if nb == ['integer', 1]: return a
        if tag == 'add':
            if na == ['integer', 0]: return b
            if nb == ['integer', 0]: return a
        if tag == 'sub':
            if nb == ['integer', 0]: return a
            if a.i == b.i: return self.coerce(0)
        if tag in ('add', 'mul') and a.i > b.i: a, b = b, a
        return self.intern((tag, a.i, b.i))

class Expr:
    def __init__(self, d, i): self.d, self.i = d, i
    def __add__(self, other): return self.d.op('add', self, other)
    def __radd__(self, other): return self.d.op('add', other, self)
    def __sub__(self, other): return self.d.op('sub', self, other)
    def __rsub__(self, other): return self.d.op('sub', other, self)
    def __mul__(self, other): return self.d.op('mul', self, other)
    def __rmul__(self, other): return self.d.op('mul', other, self)
    def __neg__(self): return self.d.op('mul', -1, self)
    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'fixed natural exponent')
        if exponent == 0: return self.d.coerce(1)
        if exponent == 1: return self
        a = self ** (exponent // 2)
        return a*a if exponent % 2 == 0 else (a*a)*self

def export(name, d, output, registers, metadata):
    live = set()
    def visit(i):
        if i in live: return
        live.add(i)
        node = d.nodes[i]
        if node[0] in ('add', 'sub', 'mul'):
            visit(node[1]); visit(node[2])
    visit(output.i)
    remap = {old: new for new, old in enumerate(sorted(live))}
    nodes = []
    for old in sorted(live):
        node = d.nodes[old]
        nodes.append([node[0], remap[node[1]], remap[node[2]]]
                     if node[0] in ('add', 'sub', 'mul') else node)
    counts = Counter(node[0] for node in nodes if node[0] in ('add', 'sub', 'mul'))
    used = {node[1] for node in nodes if node[0] == 'variable'}
    require(used == set(d.variables), 'every declared variable is live')
    return dict(schema='integer-polynomial-dag-v1', name=name,
                domain='unrestricted integers', variables=d.variables,
                variable_count=len(d.variables), nodes=nodes, output=remap[output.i],
                named_registers={key: remap[value.i] for key, value in registers.items()
                                 if value.i in remap},
                operation_counts=dict(sorted(counts.items())), operations=sum(counts.values()),
                coefficient_binding='../coefficients/BINDING.json', **metadata)

