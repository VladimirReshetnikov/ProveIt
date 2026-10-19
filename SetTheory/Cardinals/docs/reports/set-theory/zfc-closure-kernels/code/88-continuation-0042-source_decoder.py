#!/usr/bin/env python3
"""Independent structural and exact path-CFG audit of source reassociation.

No optimizer, MILP package, DAG vendor module or search certificate is imported.
The decisive semantic check compares every DFS leaf, decrement guard and
successor leaf using the literal RegisterPath consume/strip/increment rules.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LITERAL = ROOT / 'vendor/context246/sources/Prog254.v'
EXPECTED_LITERAL_HASH = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(x):
    return json.dumps(x, separators=(',', ':')).encode()


def read_json(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    nodes = {int(i): tuple(tuple(e) for e in pair) for i, pair in data['nodes'].items()}
    return nodes, data['root'], sha(raw)


def read_literal(path):
    raw = path.read_bytes()
    assert sha(raw) == EXPECTED_LITERAL_HASH
    body = raw.decode().split('Definition p254_tab', 1)[1].split(':= [', 1)[1].split('].', 1)[0]
    pattern = re.compile(r'\((CN|CI|CD|CB|CC|CH)(?: (\d+))?,\s*(CN|CI|CD|CB|CC|CH)(?: (\d+))?\)')
    def edge(op, number):
        return (op[1], int(number)) if number else (op[1],)
    pairs = [(edge(a, b), edge(c, d)) for a, b, c, d in pattern.findall(body)]
    assert len(pairs) == 6459 and not re.sub(r'[\s;]', '', pattern.sub('', body))
    return dict(enumerate(pairs)), 0


class Decoder:
    def __init__(self, nodes, root):
        self.nodes = nodes
        self.root = root
        active = set()
        reached = set()
        self.sites = []
        def walk(e, word):
            if e[0] != 'N':
                assert e[0] in ('I', 'D', 'B', 'C', 'H')
                assert len(e) == (1 if e[0] == 'H' else 2)
                if len(e) == 2:
                    assert isinstance(e[1], int) and e[1] >= 0
                self.sites.append((word, e))
                return
            n = e[1]
            assert n in nodes and n not in active
            active.add(n)
            reached.add(n)
            a, b = nodes[n]
            walk(a, word + '0')
            walk(b, word + '1')
            active.remove(n)
        walk(('N', root), '')
        self.reached = reached
        self.byword = {word: i for i, (word, _) in enumerate(self.sites)}
        assert len(self.byword) == len(self.sites)

    @lru_cache(None)
    def tree(self, e):
        if e[0] != 'N':
            return e
        a, b = self.nodes[e[1]]
        return ('N', self.tree(a), self.tree(b))

    @lru_cache(None)
    def bounds(self, e):
        if e[0] != 'N':
            return (e[1] if e[0] == 'B' else int(e[0] == 'D'),
                    e[1] if e[0] == 'C' else 0)
        a, b = self.nodes[e[1]]
        ba, ca = self.bounds(a)
        bb, cb = self.bounds(b)
        return max(ba - 1, bb), max(ca, cb - 1)

    @lru_cache(None)
    def normal(self, e):
        if e[0] != 'N':
            return ('L', e)
        a, b = self.nodes[e[1]]
        aa, bb = self.normal(a), self.normal(b)
        if self.bounds(a) == self.bounds(b) == (0, 0):
            left = aa[1] if aa[0] == 'S' else (aa,)
            right = bb[1] if bb[0] == 'S' else (bb,)
            return ('S', left + right)
        return ('A', aa, bb)

    def leaf(self, path):
        e = ('N', self.root)
        d = 0
        word = ''
        while e[0] == 'N':
            b = int(path[d]) if d < len(path) else 0
            word += str(b)
            e = self.nodes[e[1]][b]
            d += 1
            assert d <= len(self.nodes) + 1
        return self.byword[word]

    @staticmethod
    def increment(path):
        if not path:
            return ''
        return format((int(path, 2) + 1) % (1 << len(path)), f'0{len(path)}b')

    @staticmethod
    def strip(path, bit, k):
        at = len(path)
        while k and at:
            at -= 1
            if path[at] == bit:
                k -= 1
        return path[:at]

    def graph(self):
        out = []
        for word, e in self.sites:
            op = e[0]
            if op == 'I':
                successors = (self.leaf(self.increment(word)),)
            elif op == 'D':
                successors = (self.leaf(self.increment(word)),
                              self.leaf(self.increment(self.strip(word, '0', 1))))
            elif op == 'B':
                successors = (self.leaf(self.increment(self.strip(word, '0', e[1]))),)
            elif op == 'C':
                successors = (self.leaf(self.strip(word, '1', e[1])),)
            else:
                successors = ()
            out.append((e, successors))
        return out

    def metrics(self):
        @lru_cache(None)
        def go(e):
            if e[0] != 'N':
                return 0, 0, 0
            a, b = (go(x) for x in self.nodes[e[1]])
            prefix = a[0] + 1
            return prefix, max(prefix, a[1], b[1]), 1 + max(a[2], b[2])
        return go(('N', self.root))

