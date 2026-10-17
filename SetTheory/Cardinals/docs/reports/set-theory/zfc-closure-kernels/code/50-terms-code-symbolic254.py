#!/usr/bin/env python3
"""Exact C254 checking using sparse proof trees and symbolic Cantor terms.

No materialization of intermediate formula integers is required.  This is a
new reference implementation, NOT a binary TM or a Lean-verified program.
All axiom terms are extracted from the pinned original Code254.lean.
"""
from dataclasses import dataclass
from functools import lru_cache
import json
from math import isqrt
from pathlib import Path

SPEC = json.loads((Path(__file__).resolve().parents[1] /
                   'data/spec254.json').read_text())['definitions']
ARITY = (0, 1, 1, 2, 3, 3, 3, 3, 2, 3, 4, 3)


def pair(a, b):
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(n):
    if type(n) is not int or n < 0:
        raise ValueError('Expected a natural number')
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def check_pair_witness(n, a, b):
    """Polynomial graph; the certificate verifier does not call unpair."""
    return (all(type(x) is int and x >= 0 for x in (n, a, b)) and
            2 * n == (a + b) * (a + b + 1) + 2 * b)


class Arena:
    """Topologically ordered, shared expressions for natural numbers.

    ('n', v) denotes v; ('b', tag, x, y) denotes 4*P(x,y)+tag.
    Only the exact zero-argument simplification B_tag(0,0)=tag is performed.
    """
    def __init__(self):
        self.nodes = []
        self.index = {}
        self.frozen = False
        self.equalities = []
        self.eq_cache = {}
        self.comparisons = 0
        self.literal(0)

    def intern(self, node):
        if node in self.index:
            return self.index[node]
        if self.frozen:
            raise ValueError('Certificate omitted an expression node')
        ans = len(self.nodes)
        self.nodes.append(node)
        self.index[node] = ans
        return ans

    def literal(self, n):
        if type(n) is not int or n < 0:
            raise ValueError('Non-natural literal')
        return self.intern(('n', n))

    def b(self, tag, x, y):
        if tag not in range(4):
            raise ValueError('Invalid formula tag')
        if x == 0 and y == 0:
            return self.literal(tag)
        return self.intern(('b', tag, x, y))

    def apply(self, name, args):
        if name in ('wim', 'wel', 'wal', 'weq'):
            return self.b(('wim', 'wel', 'wal', 'weq').index(name), *args)
        if name == 'wn':
            return self.apply('wim', [args[0], self.literal(1)])
        if name == 'wa':
            return self.apply('wn', [self.apply('wim', [args[0],
                                      self.apply('wn', [args[1]])])])
        if name == 'wex':
            return self.apply('wn', [self.apply('wal', [args[0],
                                      self.apply('wn', [args[1]])])])
        spec = SPEC[name]
        env = dict(zip(spec['parameters'], args, strict=True))

        def ev(term):
            if type(term) is int:
                return self.literal(term)
            if type(term) is str:
                return self.literal(1) if term == 'F' else env[term]
            return self.apply(term[0], [ev(t) for t in term[1:]])

        return ev(spec['term'])

    def prove_equal(self, x, y):
        """Return a local equality-certificate index, or None if unequal.

        Cantor inversion is confined to this certificate producer.  Its
        witnesses are checked by a polynomial identity in verify_certificate.
        """
        key = x, y
        if key in self.eq_cache:
            return self.eq_cache[key]
        self.comparisons += 1
        nx, ny = self.nodes[x], self.nodes[y]
        rule, premises, witness = None, [], []
        if x == y:
            rule = 'refl'
        elif nx[0] == ny[0] == 'n':
            if nx[1] == ny[1]:
                rule = 'literal'
        elif nx[0] == ny[0] == 'b':
            if nx[1] == ny[1]:
                i = self.prove_equal(nx[2], ny[2])
                j = self.prove_equal(nx[3], ny[3]) if i is not None else None
                if i is not None and j is not None:
                    rule, premises = 'bb', [i, j]
        else:
            literal_left = nx[0] == 'n'
            lit, built = (nx, ny) if literal_left else (ny, nx)
            n = lit[1]
            tag = n % 4
            if built[1] == tag:
                a, b = unpair(n // 4)
                ai, bi = self.literal(a), self.literal(b)
                pairs = ((ai, built[2]), (bi, built[3])) if literal_left else (
                         (built[2], ai), (built[3], bi))
                i = self.prove_equal(*pairs[0])
                j = self.prove_equal(*pairs[1]) if i is not None else None
                if i is not None and j is not None:
                    rule = 'lb' if literal_left else 'bl'
                    premises, witness = [i, j], [ai, bi]
        if rule is None:
            self.eq_cache[key] = None
            return None
        ans = len(self.equalities)
        self.equalities.append({'pair': [x, y], 'rule': rule,
                                'premises': premises, 'witness': witness})
        self.eq_cache[key] = ans
        return ans

    def equal(self, x, y):
        return self.prove_equal(x, y) is not None

    def bit_bounds(self, root):
        """Certified elementary lower/upper bit-length bounds, no expansion."""
        @lru_cache(None)
        def visit(i):
            n = self.nodes[i]
            if n[0] == 'n':
                return (n[1].bit_length(),) * 2
            ax, ay = visit(n[2]), visit(n[3])
            lo, hi = max(ax[0], ay[0]), max(ax[1], ay[1])
            if hi == 0:
                return (n[1].bit_length(),) * 2
            return 2 * lo, 2 * hi + 3
        return visit(root)

    def materialize(self, root, max_bits=100000):
        """Optional QA only.  Not called by either certificate checker."""
        if self.bit_bounds(root)[1] > max_bits:
            raise OverflowError('QA materialization limit')
        @lru_cache(None)
        def visit(i):
            n = self.nodes[i]
            return n[1] if n[0] == 'n' else 4 * pair(visit(n[2]), visit(n[3])) + n[1]
        return visit(root)


@dataclass(frozen=True)
class Raw:
    tag: int
    args: tuple = ()
    children: tuple = ()

    def quote(self):
        fields = list(self.args)
        if self.tag in (1, 2):
            fields += [p.quote() for p in self.children]
        payload = fields[-1] if fields else 0
        for n in reversed(fields[:-1]):
            payload = pair(n, payload)
        return 12 * payload + self.tag + 1

    def measures(self):
        sub = [p.measures() for p in self.children]
        size = 1 + sum(s for s, _, _ in sub)
        height = 1 + max((h for _, h, _ in sub), default=0)
        product = 1
        for v in self.args:
            product *= v + 1
        for _, _, p in sub:
            product *= p
        return size, height, product


def parse(code):
    """Parse only recursive dependencies.  Zero is invalid, truth is code1."""
    @lru_cache(None)
    def visit(c):
        if type(c) is not int or c <= 0:
            return None
        tag, payload = (c - 1) % 12, (c - 1) // 12
        if tag == 0:
            return Raw(0) if payload == 0 else None
        a, tail = unpair(payload)
        b, d = unpair(tail)
        if tag == 1:
            p, q = visit(b), visit(d)
            return Raw(1, (a,), (p, q)) if p is not None and q is not None else None
        if tag == 2:
            p = visit(tail)
            return Raw(2, (a,), (p,)) if p is not None else None
        if tag in (3, 8):
            return Raw(tag, (a, tail))
        if tag == 10:
            e, f = unpair(d)
            return Raw(tag, (a, b, e, f))
        return Raw(tag, (a, b, d))
    return visit(code)


def build(raw, arena):
    """Return (formula expression, validity, postorder proof records)."""
    rows = []

    def visit(p):
        children = [visit(t) for t in p.children]
        valid = all(x[1] for x in children)
        ai = [arena.literal(v) for v in p.args]
        eq = None
        if p.tag == 0:
            out = 0
        elif p.tag == 1:
            out = ai[0]
            major = arena.apply('wim', [children[0][0], out])
            eq = arena.prove_equal(children[1][0], major)
            valid = valid and eq is not None
        elif p.tag == 2:
            out = arena.apply('wal', [ai[0], children[0][0]])
        elif p.tag == 11:
            out = arena.apply('bundle', ai)
            valid = valid and p.args[2] != p.args[0] and p.args[2] != p.args[1]
        else:
            out = arena.apply('rho' + str(p.tag - 2), ai)
        i = len(rows)
        rows.append({'tag': p.tag, 'args': list(p.args),
                     'children': [x[2] for x in children],
                     'formula': out, 'mp_equality': eq})
        return out, valid, i

    out, valid, _ = visit(raw)
    return out, valid, rows


def check(code, conclusion):
    if type(conclusion) is not int or conclusion < 0:
        return False
    raw = parse(code)
    if raw is None:
        return False
    arena = Arena()
    out, valid, _ = build(raw, arena)
    return valid and arena.equal(out, arena.literal(conclusion))


def make_certificate(raw, conclusion):
    arena = Arena()
    out, valid, rows = build(raw, arena)
    final = arena.prove_equal(out, arena.literal(conclusion))
    if not valid or final is None:
        raise ValueError('Not an accepted proof of the requested conclusion')
    return {'format': 'sparse-c254-v1', 'conclusion': conclusion,
            'nodes': [list(n) for n in arena.nodes],
            'equalities': arena.equalities, 'proof_rows': rows,
            'final_equality': final}


def verify_certificate(cert):
    """Independent local certificate checker; NO square root or unpair call.

    This intentionally does not inspect the legacy numeric proof quote.
    Existence of these certificates is equivalent to C254 derivability.
    """
    try:
        if cert['format'] != 'sparse-c254-v1':
            return False
        arena = Arena()
        nodes = cert['nodes']
        if not nodes or nodes[0] != ['n', 0]:
            return False
        arena.nodes, arena.index = [], {}
        for i, raw in enumerate(nodes):
            n = tuple(raw)
            if len(n) == 2 and n[0] == 'n':
                if type(n[1]) is not int or n[1] < 0:
                    return False
            elif len(n) == 4 and n[0] == 'b':
                if type(n[1]) is not int or not 0 <= n[1] < 4:
                    return False
                if not all(type(j) is int and 0 <= j < i for j in n[2:]):
                    return False
                if n[2:] == (0, 0):
                    return False
            else:
                return False
            if n in arena.index:
                return False
            arena.index[n] = i
            arena.nodes.append(n)
        arena.frozen = True
        eqpairs = []
        for step in cert['equalities']:
            x, y = step['pair']
            if not all(type(j) is int and 0 <= j < len(nodes) for j in (x, y)):
                return False
            nx, ny = nodes[x], nodes[y]
            rule, pre, wit = step['rule'], step['premises'], step['witness']
            if rule == 'refl':
                good = x == y and pre == [] and wit == []
            elif rule == 'literal':
                good = nx[0] == ny[0] == 'n' and nx[1] == ny[1] and pre == [] and wit == []
            else:
                if len(pre) != 2 or not all(type(i) is int and 0 <= i < len(eqpairs) for i in pre):
                    return False
                if rule == 'bb':
                    good = (nx[0] == ny[0] == 'b' and nx[1] == ny[1] and wit == [] and
                            eqpairs[pre[0]] == (nx[2], ny[2]) and
                            eqpairs[pre[1]] == (nx[3], ny[3]))
                elif rule in ('lb', 'bl'):
                    if len(wit) != 2 or not all(type(i) is int and 0 <= i < len(nodes) for i in wit):
                        return False
                    na, nb = nodes[wit[0]], nodes[wit[1]]
                    lit, built = (nx, ny) if rule == 'lb' else (ny, nx)
                    if lit[0] != 'n' or built[0] != 'b' or na[0] != 'n' or nb[0] != 'n':
                        return False
                    # Equivalent to n = 4*P(a,b)+tag, entirely polynomial.
                    a, b, n, tag = na[1], nb[1], lit[1], built[1]
                    polynomial_ok = n == 2 * (a + b) * (a + b + 1) + 4 * b + tag
                    wanted = ((wit[0], built[2]), (wit[1], built[3])) if rule == 'lb' else (
                              (built[2], wit[0]), (built[3], wit[1]))
                    good = polynomial_ok and tuple(eqpairs[i] for i in pre) == wanted
                else:
                    return False
            if not good:
                return False
            eqpairs.append((x, y))
        formulas = []
        for i, row in enumerate(cert['proof_rows']):
            tag, args, children = row['tag'], row['args'], row['children']
            if type(tag) is not int or not 0 <= tag < 12 or len(args) != ARITY[tag]:
                return False
            if not all(type(v) is int and v >= 0 for v in args):
                return False
            if len(children) != (2 if tag == 1 else 1 if tag == 2 else 0):
                return False
            if not all(type(j) is int and 0 <= j < i for j in children):
                return False
            ai = [arena.literal(v) for v in args]
            if tag == 0:
                out = 0
            elif tag == 1:
                out = ai[0]
                major = arena.apply('wim', [formulas[children[0]], out])
                eq = row['mp_equality']
                if type(eq) is not int or not 0 <= eq < len(eqpairs):
                    return False
                if eqpairs[eq] != (formulas[children[1]], major):
                    return False
            elif tag == 2:
                out = arena.apply('wal', [ai[0], formulas[children[0]]])
            elif tag == 11:
                if args[2] == args[0] or args[2] == args[1]:
                    return False
                out = arena.apply('bundle', ai)
            else:
                out = arena.apply('rho' + str(tag - 2), ai)
            if row['formula'] != out or (tag != 1 and row['mp_equality'] is not None):
                return False
            formulas.append(out)
        if not formulas:
            return False
        final = cert['final_equality']
        if type(final) is not int or not 0 <= final < len(eqpairs):
            return False
        return eqpairs[final] == (formulas[-1], arena.literal(cert['conclusion']))
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        return False
