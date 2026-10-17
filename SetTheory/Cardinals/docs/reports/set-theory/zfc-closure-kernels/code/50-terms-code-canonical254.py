#!/usr/bin/env python3
"""Canonical constructor certificates for the exact twelve-rule C254 calculus.

The producer may compute Cantor inverses. The independent certificate verifier
checks only forward polynomial identities, bounded indices and fixed terms.
"""
from functools import lru_cache
from symbolic254 import Arena, ARITY, build, parse, unpair, pair


def quote_rows(rows):
    """Forward quote equations only; useful for an exact legacy-code link."""
    codes = []
    for row in rows:
        fields = list(row['args']) + [codes[j] for j in row['children']]
        payload = fields[-1] if fields else 0
        for v in reversed(fields[:-1]):
            payload = pair(v, payload)
        codes.append(12 * payload + row['tag'] + 1)
    return codes


class CanonicalArena(Arena):
    def __init__(self):
        self.nodes = [('z',)]
        self.index = {('z',): 0}
        self.frozen = False
        self.literals = [{'value': 0, 'node': 0, 'parts': []}]
        self.literal_index = {0: 0}
        self.comparisons = 0

    def literal(self, n):
        if type(n) is not int or n < 0:
            raise ValueError('Expected a natural literal')
        if n in self.literal_index:
            return self.literals[self.literal_index[n]]['node']
        if self.frozen:
            raise ValueError('Missing literal witness')
        a, b = unpair(n // 4)
        na, nb = self.literal(a), self.literal(b)
        root = self.b(n % 4, na, nb)
        self.literal_index[n] = len(self.literals)
        self.literals.append({'value': n, 'node': root,
                              'parts': [self.literal_index[a], self.literal_index[b]]})
        return root

    def b(self, tag, x, y):
        if type(tag) is not int or not 0 <= tag < 4:
            raise ValueError('Invalid constructor tag')
        if tag == 0 and x == 0 and y == 0:
            return 0
        return self.intern(('b', tag, x, y))

    def prove_equal(self, x, y):
        self.comparisons += 1
        return 0 if x == y else None

    def equal(self, x, y):
        return x == y

    def bit_bounds(self, root):
        @lru_cache(None)
        def visit(i):
            if i == 0:
                return 0, 0
            _, tag, x, y = self.nodes[i]
            ax, ay = visit(x), visit(y)
            lo, hi = max(ax[0], ay[0]), max(ax[1], ay[1])
            if hi == 0:
                return (tag.bit_length(),) * 2
            return 2 * lo, 2 * hi + 3
        return visit(root)

    def materialize(self, root, max_bits=100000):
        if self.bit_bounds(root)[1] > max_bits:
            raise OverflowError('QA materialization limit')
        @lru_cache(None)
        def visit(i):
            if i == 0:
                return 0
            _, tag, x, y = self.nodes[i]
            return 4 * pair(visit(x), visit(y)) + tag
        return visit(root)


def check(code, conclusion):
    if type(conclusion) is not int or conclusion < 0:
        return False
    raw = parse(code)
    if raw is None:
        return False
    arena = CanonicalArena()
    out, valid, _ = build(raw, arena)
    return valid and out == arena.literal(conclusion)


def make_certificate(raw, conclusion, quoted=True):
    arena = CanonicalArena()
    out, valid, rows = build(raw, arena)
    final = arena.literal(conclusion)
    if not valid or out != final:
        raise ValueError('Not an accepted proof of the requested conclusion')
    for row in rows:
        del row['mp_equality']
    cert = {'format': 'canonical-c254-v1', 'conclusion': conclusion,
            'nodes': [list(n) for n in arena.nodes],
            'literals': arena.literals, 'proof_rows': rows}
    if quoted:
        codes = quote_rows(rows)
        cert.update(source_code=codes[-1], proof_codes=codes)
    return cert


def verify_certificate(cert):
    """Total rejecting checker for finite JSON-like certificates.

    There is no Cantor inverse, numeric formula evaluation, proof search,
    arbitrary-formula oracle, or recursive comparison in this routine.
    """
    try:
        if cert['format'] != 'canonical-c254-v1':
            return False
        nodes = cert['nodes']
        if not nodes or nodes[0] != ['z']:
            return False
        arena = CanonicalArena()
        for i, raw in enumerate(nodes[1:], 1):
            if len(raw) != 4 or raw[0] != 'b':
                return False
            _, tag, x, y = raw
            if type(tag) is not int or not 0 <= tag < 4:
                return False
            if not all(type(j) is int and 0 <= j < i for j in (x, y)):
                return False
            if (tag, x, y) == (0, 0, 0) or tuple(raw) in arena.index:
                return False
            arena.index[tuple(raw)] = i
            arena.nodes.append(tuple(raw))
        literals = cert['literals']
        if not literals or literals[0] != {'value': 0, 'node': 0, 'parts': []}:
            return False
        if type(literals[0]['value']) is not int or type(literals[0]['node']) is not int:
            return False
        for i, row in enumerate(literals[1:], 1):
            value, root, refs = row['value'], row['node'], row['parts']
            if type(value) is not int or value <= 0 or value in arena.literal_index:
                return False
            if type(root) is not int or not 0 < root < len(nodes):
                return False
            if len(refs) != 2 or not all(type(j) is int and 0 <= j < i for j in refs):
                return False
            aa, bb = literals[refs[0]], literals[refs[1]]
            a, b = aa['value'], bb['value']
            _, tag, x, y = nodes[root]
            if x != aa['node'] or y != bb['node']:
                return False
            if value != 2 * (a + b) * (a + b + 1) + 4 * b + tag:
                return False
            arena.literal_index[value] = i
            arena.literals.append(dict(row))
        arena.frozen = True
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
                if formulas[children[1]] != arena.apply('wim', [formulas[children[0]], out]):
                    return False
            elif tag == 2:
                out = arena.apply('wal', [ai[0], formulas[children[0]]])
            elif tag == 11:
                if args[2] == args[0] or args[2] == args[1]:
                    return False
                out = arena.apply('bundle', ai)
            else:
                out = arena.apply('rho' + str(tag - 2), ai)
            if type(row['formula']) is not int or row['formula'] != out:
                return False
            formulas.append(out)
        if not formulas or formulas[-1] != arena.literal(cert['conclusion']):
            return False
        if 'source_code' in cert or 'proof_codes' in cert:
            source, codes = cert['source_code'], cert['proof_codes']
            if type(source) is not int or source <= 0:
                return False
            if len(codes) != len(cert['proof_rows']):
                return False
            if not all(type(c) is int and c > 0 for c in codes):
                return False
            # Use supplied child codes locally and reject the first false row.
            # Reconstructing the entire quotation here could expand exponentially
            # on a short malicious DAG with falsely small claimed code labels.
            for i, row in enumerate(cert['proof_rows']):
                fields = list(row['args']) + [codes[j] for j in row['children']]
                payload = fields[-1] if fields else 0
                for v in reversed(fields[:-1]):
                    payload = pair(v, payload)
                if codes[i] != 12 * payload + row['tag'] + 1:
                    return False
            if codes[-1] != source:
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        return False
