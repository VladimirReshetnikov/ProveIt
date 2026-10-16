#!/usr/bin/env python3
"""Locally nameless binding certificates and a PSC Hilbert reference checker.

The checker validates explicit opening, closing and two-slot plugging witnesses.
It never chooses a fresh variable or implements alpha-renaming. Formula DAGs are
acyclic, and all checker traversals are iterative. This is an executable specification,
not a compiled Turing machine or a machine-checked soundness proof.

Terms: ('f', name), ('b', index). Formulas: bot, mem, imp, all (no binder name).
Witness rows: [source_formula, output_formula, depth, child_witness_ids].
See report.tex for the exact semantics and soundness/completeness arguments.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class Invalid(ValueError):
    """Malformed syntax, invalid certificate, or failed inference condition."""


def nat(x):
    if type(x) is not int or x < 0:
        raise Invalid('expected a nonnegative integer, excluding bool')
    return x


def term(x):
    if not isinstance(x, (list, tuple)) or len(x) != 2 or x[0] not in ('f', 'b'):
        raise Invalid('invalid term')
    return (x[0], nat(x[1]))


def F(x): return ('f', nat(x))
def B(x): return ('b', nat(x))


class Arena:
    def __init__(self):
        self.nodes = []
        self.intern = {}
        self.bot = self.add(('bot',))

    def ref(self, p):
        p = nat(p)
        if p >= len(self.nodes):
            raise Invalid('formula reference out of range')
        return p

    def add(self, node):
        if not isinstance(node, (list, tuple)) or not node:
            raise Invalid('invalid formula node')
        node = tuple(node)
        if node[0] == 'bot' and len(node) == 1:
            pass
        elif node[0] == 'mem' and len(node) == 3:
            node = ('mem', term(node[1]), term(node[2]))
        elif node[0] == 'imp' and len(node) == 3:
            node = ('imp', self.ref(node[1]), self.ref(node[2]))
        elif node[0] == 'all' and len(node) == 2:
            node = ('all', self.ref(node[1]))
        else:
            raise Invalid('invalid formula node')
        if node not in self.intern:
            self.intern[node] = len(self.nodes)
            self.nodes.append(node)
        return self.intern[node]

    def mem(self, x, y): return self.add(('mem', x, y))
    def imp(self, p, q): return self.add(('imp', p, q))
    def all(self, p): return self.add(('all', p))
    def neg(self, p): return self.imp(p, self.bot)
    def ex(self, p): return self.neg(self.all(self.neg(p)))
    def conj(self, p, q): return self.neg(self.imp(p, self.neg(q)))
    def disj(self, p, q): return self.imp(self.neg(p), q)

    def scoped(self, p, depth=0):
        pending, seen = [(self.ref(p), nat(depth))], set()
        while pending:
            p, d = pending.pop()
            if (p, d) in seen:
                continue
            seen.add((p, d))
            n = self.nodes[p]
            if n[0] == 'mem':
                if any(t[0] == 'b' and t[1] >= d for t in n[1:]):
                    return False
            elif n[0] == 'imp':
                pending.extend(((n[1], d), (n[2], d)))
            elif n[0] == 'all':
                pending.append((n[1], d + 1))
        return True

    @classmethod
    def load(cls, nodes):
        if not isinstance(nodes, list) or not nodes:
            raise Invalid('expected a nonempty formula table')
        a = cls()
        if nodes[0] not in (['bot'], ('bot',)):
            raise Invalid('formula zero must be Bottom')
        for i, node in enumerate(nodes[1:], 1):
            if a.add(node) != i:
                raise Invalid('formula table must be interned and topological')
        return a


@dataclass(frozen=True)
class Mode:
    kind: str
    a: int
    b: int = 0
    width: int = 0

    def validate(self):
        nat(self.a); nat(self.b); nat(self.width)
        if self.kind not in ('open', 'close', 'plug'):
            raise Invalid('unknown binding mode')
        if self.kind == 'plug':
            if not (self.a < self.width and self.b < self.width):
                raise Invalid('plug slots outside surrounding binder block')
        elif self.b != 0 or self.width != 0:
            raise Invalid('extraneous mode parameters')
        return self

    def map_term(self, t, d):
        """Local term rule, with its source-scope check."""
        t, d = term(t), nat(d)
        kind, k = t
        limit = d + (1 if self.kind == 'open' else 0)
        if kind == 'b':
            if k >= limit:
                raise Invalid('dangling bound index in binding witness')
            if self.kind == 'open' and k == d:
                return F(self.a)
            return t
        if self.kind == 'close' and k == self.a:
            return B(d)
        if self.kind == 'plug' and k in (0, 1):
            return B(d + (self.a if k == 0 else self.b))
        return t


def produce(arena, source, mode):
    """Produce a finite witness. Correctness is checked by verify(), below."""
    mode.validate()
    source = arena.ref(source)
    memo, rows = {}, []
    todo = [(source, 0, False)]
    while todo:
        p, d, ready = todo.pop()
        if (p, d) in memo:
            continue
        n = arena.nodes[p]
        children = [(q, d) for q in n[1:]] if n[0] == 'imp' else (
            [(n[1], d + 1)] if n[0] == 'all' else [])
        if not ready and children:
            todo.append((p, d, True))
            todo.extend((q, e, False) for q, e in reversed(children))
            continue
        refs = [memo[c] for c in children]
        outputs = [rows[r][1] for r in refs]
        if n[0] == 'bot': out = arena.bot
        elif n[0] == 'mem':
            out = arena.mem(mode.map_term(n[1], d), mode.map_term(n[2], d))
        elif n[0] == 'imp': out = arena.imp(*outputs)
        else: out = arena.all(outputs[0])
        memo[p, d] = len(rows)
        rows.append([p, out, d, refs])
    return {'mode': [mode.kind, mode.a, mode.b, mode.width],
            'source': source, 'output': rows[-1][1], 'rows': rows}


def verify(arena, certificate, expected_mode=None, source=None, output=None):
    """Check local equations and backward witness references, without produce()."""
    if not isinstance(certificate, dict) or set(certificate) != {
            'mode', 'source', 'output', 'rows'}:
        raise Invalid('invalid witness envelope')
    params = certificate['mode']
    if not isinstance(params, (list, tuple)) or len(params) != 4:
        raise Invalid('invalid mode header')
    mode = Mode(*params).validate()
    if expected_mode is not None and mode != expected_mode:
        raise Invalid('binding mode does not match rule')
    src, dst = arena.ref(certificate['source']), arena.ref(certificate['output'])
    if source is not None and src != source:
        raise Invalid('wrong witness input')
    if output is not None and dst != output:
        raise Invalid('wrong witness output')
    rows = certificate['rows']
    if not isinstance(rows, list) or not rows:
        raise Invalid('empty witness')
    checked = []
    for i, row in enumerate(rows):
        if not isinstance(row, (list, tuple)) or len(row) != 4:
            raise Invalid('invalid witness row')
        p, q, d, refs = row
        p, q, d = arena.ref(p), arena.ref(q), nat(d)
        if not isinstance(refs, (list, tuple)):
            raise Invalid('invalid child-reference list')
        refs = [nat(r) for r in refs]
        if any(r >= i for r in refs):
            raise Invalid('witness dependency is not earlier')
        left, right = arena.nodes[p], arena.nodes[q]
        if left[0] != right[0]:
            raise Invalid('constructor changed')
        if left[0] == 'bot':
            expected = []
        elif left[0] == 'mem':
            expected = []
            if tuple(mode.map_term(t, d) for t in left[1:]) != right[1:]:
                raise Invalid('incorrect local term transformation')
        elif left[0] == 'imp':
            expected = [(left[1], right[1], d), (left[2], right[2], d)]
        else:
            expected = [(left[1], right[1], d + 1)]
        if [checked[r] for r in refs] != expected:
            raise Invalid('incorrect child witnesses or binder depth')
        checked.append((p, q, d))
    if checked[-1] != (src, dst, 0):
        raise Invalid('incorrect root witness')
    return dst


def psc(arena, matrix, certificates):
    """Construct the exact curried subset PSC from three checked slot maps.

    Free names 0 and 1 designate the matrix input and output. Other free names
    remain unrestricted parameters; the resulting open instance is an axiom.
    Its universal closure is interderivable in the specified full calculus.
    """
    if len(certificates) != 3:
        raise Invalid('PSC needs exactly three binding witnesses')
    modes = [Mode('plug', 2, 0, 3), Mode('plug', 1, 0, 4), Mode('plug', 0, 1, 4)]
    local_phi, closed_phi, support_phi = [verify(arena, c, m, source=matrix)
                                        for c, m in zip(certificates, modes)]
    mem, imp, all_ = arena.mem, arena.imp, arena.all
    # Under x,b,y: y is index0, b index1, x index2.
    sub_y_b = all_(imp(mem(B(0), B(1)), mem(B(0), B(2))))
    local = all_(arena.ex(all_(imp(local_phi, sub_y_b))))
    # Under a,c,x: x is index0, c index1, a index2.
    sub_x_a = all_(imp(mem(B(0), B(1)), mem(B(0), B(3))))
    guard = arena.disj(sub_x_a, mem(B(0), B(1)))
    closed = all_(imp(guard, all_(imp(closed_phi, mem(B(0), B(2))))))
    # Under a,c,y: y is index0, c index1; an inner x is index0.
    support = all_(imp(mem(B(0), B(1)), arena.ex(support_phi)))
    result = imp(local, all_(arena.ex(arena.conj(closed, support))))
    if not arena.scoped(result):
        raise Invalid('internal PSC scope invariant')
    return result


def check_document(document):
    """Check a finite JSON-compatible Hilbert derivation.

    Opcodes K,S,C,UI,UD,PSC,MP,GEN match the complete prior reference calculus.
    All conclusions are reconstructed; callers cannot assert an arbitrary fact.
    UI/UD/GEN/PSC additionally carry locally checkable binding witnesses.
    """
    if not isinstance(document, dict) or set(document) != {'formulas', 'lines'}:
        raise Invalid('invalid derivation envelope')
    a = Arena.load(document['formulas'])
    lines = document['lines']
    if not isinstance(lines, list):
        raise Invalid('invalid line list')
    proved = []
    for line in lines:
        if not isinstance(line, dict) or set(line) != {'rule', 'args', 'witnesses'}:
            raise Invalid('invalid proof line')
        op, args, ws = line['rule'], line['args'], line['witnesses']
        if not isinstance(args, list) or not isinstance(ws, list):
            raise Invalid('invalid line fields')
        arity = {'K': (2,0), 'S': (3,0), 'C': (2,0), 'UI': (2,1),
                 'UD': (3,2), 'PSC': (1,3), 'MP': (2,0), 'GEN': (2,1)}
        if not isinstance(op, str) or op not in arity or (len(args), len(ws)) != arity[op]:
            raise Invalid('wrong rule arity')
        for arg in args: nat(arg)
        if op in ('K', 'S', 'C'):
            if any(not a.scoped(a.ref(p)) for p in args):
                raise Invalid('propositional payload not locally closed')
            if op == 'K':
                p, q = args; out = a.imp(p, a.imp(q, p))
            elif op == 'S':
                p, q, r = args
                out = a.imp(a.imp(p, a.imp(q, r)), a.imp(a.imp(p,q), a.imp(p,r)))
            else:
                p, q = args
                out = a.imp(a.imp(a.neg(p), a.neg(q)), a.imp(q, p))
        elif op == 'UI':
            body, name = args
            opened = verify(a, ws[0], Mode('open', name), source=body)
            out = a.imp(a.all(body), opened)
        elif op == 'UD':
            p, q, name = args
            # Exact fixed-point close witness replaces a free-variable set scan.
            verify(a, ws[0], Mode('close', name), source=p, output=p)
            closed_q = verify(a, ws[1], Mode('close', name), source=q)
            out = a.imp(a.all(a.imp(p, closed_q)), a.imp(p, a.all(closed_q)))
        elif op == 'PSC': out = psc(a, args[0], ws)
        elif op == 'MP':
            i, j = args
            if i >= len(proved) or j >= len(proved):
                raise Invalid('MP line reference is not earlier')
            n = a.nodes[proved[j]]
            if n[0] != 'imp' or n[1] != proved[i]:
                raise Invalid('MP antecedent mismatch')
            out = n[2]
        else:
            i, name = args
            if i >= len(proved):
                raise Invalid('GEN line reference is not earlier')
            closed = verify(a, ws[0], Mode('close', name), source=proved[i])
            out = a.all(closed)
        if not a.scoped(out):
            raise Invalid('proof conclusion not locally closed')
        proved.append(out)
    return a, proved


def accepts_refutation(document):
    try:
        a, lines = check_document(document)
        return bool(lines) and lines[-1] == a.bot
    except Invalid:
        return False


def evaluate(arena, p, domain, relation: Callable, assignment: Callable, bound=()):
    """Independent small-model evaluator, used only for finite regression tests."""
    n = arena.nodes[p]
    if n[0] == 'bot': return False
    if n[0] == 'mem':
        def val(t): return assignment(t[1]) if t[0] == 'f' else bound[t[1]]
        return bool(relation(val(n[1]), val(n[2])))
    if n[0] == 'imp':
        return (not evaluate(arena,n[1],domain,relation,assignment,bound)
                or evaluate(arena,n[2],domain,relation,assignment,bound))
    return all(evaluate(arena,n[1],domain,relation,assignment,(x,)+bound) for x in domain)
