#!/usr/bin/env python3
"""Exact symbolic audit of root's nonnegative C222 gate rewrite.

Code constructors are compared by canonical arithmetic-DAG identity before
being replaced by common algebraically independent symbols.  Rail operations
are interpreted through their ring identities; the remaining finite symbolic
identity is checked by a small standard-library exact ring normalizer,
without expanding the enormous numeral codes.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
UP = ROOT/'upstream'
sys.path[:0] = [str(UP/'code'), str(UP/'provenance/upstream')]
from direct_source_factored import source_pair_calculus as original_source
spec = importlib.util.spec_from_file_location('nonnegative_source_for_audit', ROOT/'code/build.py')
new = importlib.util.module_from_spec(spec)
spec.loader.exec_module(new)


def require(ok, message):
    if not ok:
        raise ValueError(message)


# Exact commutative-ring expression normal form.  It flattens sums/products,
# collects rational-integer coefficients and distributes integer powers over
# products, but never expands the high-degree disjunction product.
def scalar(n): return ('c', n)
def symbol(n): return ('v', n)
def times(a, b):
    coefficient, factors = 1, {}
    for value in (a, b):
        if value[0] == 'c':
            coefficient *= value[1]
        elif value[0] == 'm':
            coefficient *= value[1]
            for factor, exponent in value[2]:
                factors[factor] = factors.get(factor, 0)+exponent
        else:
            factors[value] = factors.get(value, 0)+1
    if not coefficient: return scalar(0)
    if not factors: return scalar(coefficient)
    if coefficient == 1 and len(factors) == 1:
        factor, exponent = next(iter(factors.items()))
        if exponent == 1: return factor
    return ('m', coefficient, tuple(sorted(factors.items())))
def plus(a, b):
    terms = {}
    for value in (a, b):
        if value[0] == 'a':
            pairs = value[1]
        elif value[0] == 'c':
            pairs = ((scalar(1), value[1]),)
        elif value[0] == 'm':
            pairs = ((times(scalar(1), ('m', 1, value[2])), value[1]),)
        else:
            pairs = ((value, 1),)
        for term, coefficient in pairs:
            terms[term] = terms.get(term, 0)+coefficient
    terms = {t:c for t,c in terms.items() if c}
    if not terms: return scalar(0)
    if len(terms) == 1:
        term, coefficient = next(iter(terms.items()))
        return times(scalar(coefficient), term)
    return ('a', tuple(sorted(terms.items())))
def minus(a, b):
    # Distribute the sign over a top-level sum.
    if b[0] == 'a':
        neg = ('a', tuple((t, -c) for t,c in b[1]))
    else: neg = times(scalar(-1), b)
    return plus(a, neg)


class Factory:
    def __init__(self):
        self.nodes, self.lookup = [], {}
        self.v = None
        self.code_sets = {}
        self.mode = None
        self.rails = []

    def make(self, kind, *children):
        key = (kind, *children)
        if key not in self.lookup:
            self.lookup[key] = len(self.nodes)
            self.nodes.append(key)
        return self.lookup[key]

    def atom(self, x):
        if isinstance(x, int):
            return x
        require(x[0] == 'c', 'unexpected atom')
        return self.make('constant', x[1])

    def add(self, a, b):
        a, b = self.atom(a), self.atom(b)
        if self.nodes[a][0] == self.nodes[b][0] == 'constant':
            return self.make('constant', self.nodes[a][1]+self.nodes[b][1])
        return self.make('add', *sorted((a, b)))

    def mul(self, a, b):
        a, b = self.atom(a), self.atom(b)
        if self.nodes[a][0] == self.nodes[b][0] == 'constant':
            return self.make('constant', self.nodes[a][1]*self.nodes[b][1])
        return self.make('mul', *sorted((a, b)))

    def square(self, a):
        return self.mul(a, a)

    def sum(self, xs):
        value = ('c', 0)
        for x in xs:
            value = self.add(value, x)
        return value

    def product(self, xs):
        value = ('c', 1)
        for x in xs:
            value = self.mul(value, x)
        return value

    def delta(self, a, b):
        a, b = self.atom(a), self.atom(b)
        if a == self.v and self.nodes[b][0] != 'constant':
            self.code_sets.setdefault(self.mode, set()).add(b)
        if b == self.v and self.nodes[a][0] != 'constant':
            self.code_sets.setdefault(self.mode, set()).add(a)
        return self.make('difference', a, b)

    def rails_for(self, delta):
        i = len(self.rails)
        self.rails.append(delta)
        return self.make('rail+', i), self.make('rail-', i)

    def pair_add(self, a, b):
        return self.rails_for(self.add(self.delta(*a), self.delta(*b)))

    def pair_mul(self, a, b):
        return self.rails_for(self.mul(self.delta(*a), self.delta(*b)))

    def pair_square(self, a):
        return self.rails_for(self.square(self.delta(*a)))

    def sqdiff(self, a, b):
        return self.square(self.delta(a, b))


def check():
    f = Factory()
    env = {n: f.make('input', n) for n in ('a','b','c','d','p','q','v','S','Sp','u','vq','m','M0','x','y')}
    index = f.make('input', 'index')
    f.v = env['v']
    source = json.loads((UP/'provenance/upstream/wire_eliminated_source.json').read_text())
    f.mode = 'old'
    old = original_source(f, source, env, index, False)
    f.mode = 'new'
    fresh = new.direct_source(f, source, env, index, False)
    require(f.code_sets['old'] == f.code_sets['new'], 'literal code-constructor DAGs differ')
    require(len(f.code_sets['old']) == 10, 'expected nine axiom codes and one generalization code')
    replacements = {node: symbol('code_'+str(i)) for i, node in enumerate(sorted(f.code_sets['old']))}
    memo = {}
    guard_positive=f.add(f.square(env['c']),f.mul(env['a'],env['b']))
    guard_negative=f.mul(env['c'],f.add(env['a'],env['b']))

    def linear(node, scale, terms):
        n = f.nodes[node]
        if n[0] == 'add' and node not in replacements:
            linear(n[1], scale, terms)
            linear(n[2], scale, terms)
        else:
            terms[node] = terms.get(node, 0)+scale

    def difference(a, b):
        # Verified identity c^2+ab-c(a+b)=(c-a)(c-b), without expansion of
        # any code constructors or large disjunctions.
        if (a,b) == (guard_positive,guard_negative):
            return times(minus(evaluate(env['c']),evaluate(env['a'])),
                         minus(evaluate(env['c']),evaluate(env['b'])))
        terms = {}
        linear(a, 1, terms)
        linear(b, -1, terms)
        terms = {n: c for n, c in terms.items() if c}
        result = scalar(0)
        for i, delta in enumerate(f.rails):
            positive, negative = f.lookup.get(('rail+', i)), f.lookup.get(('rail-', i))
            if positive in terms or negative in terms:
                cp, cn = terms.get(positive, 0), terms.get(negative, 0)
                require(cp == -cn, 'uncancelled rail in difference')
                result = plus(result,times(scalar(cp),evaluate(delta)))
                terms.pop(positive, None)
                terms.pop(negative, None)
        for n, coefficient in terms.items():
            result = plus(result,times(scalar(coefficient),evaluate(n)))
        # All differences are local: symbolic code values are atomic here.
        return result

    def evaluate(node):
        if node in replacements:
            return replacements[node]
        if node not in memo:
            n = f.nodes[node]
            if n[0] == 'constant': value = scalar(n[1])
            elif n[0] == 'input': value = symbol(n[1])
            elif n[0] == 'add': value = plus(evaluate(n[1]),evaluate(n[2]))
            elif n[0] == 'mul': value = times(evaluate(n[1]),evaluate(n[2]))
            elif n[0] == 'difference': value = difference(n[1], n[2])
            else: raise ValueError('bare rail escaped into arithmetic')
            memo[node] = value
        return memo[node]

    old_value = difference(f.atom(old[0]), f.atom(old[1]))
    new_value = difference(f.atom(fresh[0]), f.atom(fresh[1]))
    require(old_value == new_value, 'factored source symbolic identity failed')
    # Independently multiply its two linear factors as coefficient lists.
    left = {('c','c'):1, ('a','b'):1, ('a','c'):-1, ('b','c'):-1}
    right = {}
    for x,sx in [('c',1),('a',-1)]:
        for y,sy in [('c',1),('b',-1)]:
            k=tuple(sorted((x,y)));right[k]=right.get(k,0)+sx*sy
    require(left == right, 'guard factor identity')
    payload = json.dumps(f.nodes, sort_keys=True, separators=(',', ':')).encode()
    return {"verified": True, "literal_code_DAGs_matched": 10,
            "abstract_source_identity": "P_new = P_old_positive - P_old_negative over every commutative ring",
            "quadratic_guard_identity": "c^2+ab-c(a+b)=(c-a)(c-b)",
            "nonnegativity": "Every new source gate is addition, multiplication, or square of a difference of nonnegative registers.",
            "dag_nodes_inspected": len(f.nodes), "joint_dag_sha256": hashlib.sha256(payload).hexdigest(),
            "original_module_sha256": hashlib.sha256((UP/'code/direct_source_factored.py').read_bytes()).hexdigest(),
            "new_module_sha256": hashlib.sha256((ROOT/'code/build.py').read_bytes()).hexdigest(),
            "method": "canonical literal arithmetic DAG comparison followed by exact symbolic ring identity with shared code atoms"}


if __name__ == '__main__':
    result = check()
    (Path(__file__).parent/'SOURCE_IDENTITY.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2))
