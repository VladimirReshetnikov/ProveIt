# Source-language utilities excerpted from the pinned K225/K226 packet.
# Original file: baseline226/verification/reconstruct227.py.
# Used unchanged below for tree syntax, closure bounds and two CFG resolvers.
# Original attribution and MIT No Attribution notice are preserved in the
# vendored K224/K225 archives; this adaptation adds no source optimization.
#!/usr/bin/env python3
"""Replay the pinned K229 -> recompiled229 -> split228 -> K227 construction.

Python 3.10+, standard library only. The source stages and the 49-atom binary
parenthesization are literal data; this program does not run a search or an
optimizer. It checks two independent source graph resolvers, all no-stray
successor conditions, complete blank startup, and the six whole-tape blocks
for the boundary fold. The unbounded source-to-binary runtime proof is a
separate required certificate.
"""
from __future__ import annotations
from collections import Counter
from functools import cache
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
START, DISPATCH, HALT = 95, 96, 254


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(data):
    return (json.dumps(data, separators=(',', ':')) + '\n').encode('ascii')


def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def leaf(node):
    return isinstance(node[0], str)


def tree(rows):
    root = {}
    for path, op, arg in rows:
        require(path and set(path) <= {'0', '1'}, 'Invalid source path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid opcode')
        require((op == 'CH' and arg is None) or
                (op != 'CH' and type(arg) is int and arg >= 0), 'Invalid operand')
        require(op not in ('CI', 'CD') or arg < 9, 'Invalid register')
        require(op not in ('CB', 'CC') or arg >= 1, 'Invalid control depth')
        at = root
        for bit in path:
            require('instruction' not in at, 'Overlapping source paths')
            at = at.setdefault(bit, {})
        require(not at, 'Duplicate or overlapping source path')
        at['instruction'] = (op, arg)
    def visit(node):
        if 'instruction' in node:
            require(set(node) == {'instruction'}, 'Leaf has children')
            return node['instruction']
        require(set(node) == {'0', '1'}, 'Source tree is not full')
        return visit(node['0']), visit(node['1'])
    result = visit(root)
    require(sites(result) == rows, 'Source rows are not in canonical ordinal order')
    return result


def sites(node, prefix=''):
    if leaf(node):
        return [[prefix, *node]]
    return sites(node[0], prefix + '0') + sites(node[1], prefix + '1')


@cache
def boundary(node):
    if leaf(node):
        op, arg = node
        if op == 'CD': return 1, 0, False
        if op == 'CB': return arg, 0, False
        if op == 'CC': return 0, arg, False
        return 0, 0, op == 'CH'
    a, b = boundary(node[0]), boundary(node[1])
    return (max(max(a[0] - 1, 0), b[0]),
            max(a[1], max(b[1] - 1, 0)), a[2] or b[2])


def metrics(root):
    seen = set()
    def visit(node):
        if node in seen: return
        seen.add(node)
        if not leaf(node):
            visit(node[0]); visit(node[1])
    visit(root)
    rows = sites(root)
    return {'dag_nodes': len(seen), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def graph_arithmetic(rows):
    """Binary successor/cut resolver, including the no-stray-suffix premise."""
    leaves = {p: i for i, (p, _, _) in enumerate(rows)}
    depth = max(map(len, leaves))
    checks = 0
    def locate(prefix):
        nonlocal checks
        word = prefix + '0' * depth
        for length in range(1, depth + 1):
            if word[:length] in leaves:
                require('1' not in prefix[length:], 'Stray one beyond successor leaf')
                checks += 1
                return leaves[word[:length]]
        raise ValueError('Successor has no leaf')
    def increment(path):
        if not path: return ''
        return format((int(path, 2) + 1) % (1 << len(path)), '0' + str(len(path)) + 'b')
    def cut(path, edge, level):
        positions = [i for i, bit in enumerate(path) if bit == edge]
        return path[:positions[-level]] if len(positions) >= level else ''
    graph = []
    for path, op, arg in rows:
        if op == 'CI':
            effect, targets = ['increment', arg], [locate(increment(path))]
        elif op == 'CD':
            effect = ['decrement', arg]
            targets = [locate(increment(cut(path, '0', 1))), locate(increment(path))]
        elif op == 'CB':
            effect, targets = ['identity'], [locate(increment(cut(path, '0', arg)))]
        elif op == 'CC':
            effect, targets = ['identity'], [locate(cut(path, '1', arg))]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    require(locate('') == 0, 'Initial ordinal leaf is not zero')
    return graph, checks


def graph_intervals(rows):
    """Independent resolver: subtree intervals and outward ancestor walking."""
    indices = {path: i for i, (path, _, _) in enumerate(rows)}
    intervals = {}
    def visit(path):
        if path in indices:
            answer = indices[path], indices[path] + 1
        else:
            a, b = visit(path + '0'), visit(path + '1')
            require(a[1] == b[0], 'Noncontiguous source subtree')
            answer = a[0], b[1]
        intervals[path] = answer
        return answer
    require(visit('') == (0, len(rows)), 'Source interval census')
    def unwind(path, edge, count):
        while path:
            last, path = path[-1], path[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return intervals[path][1] % len(rows) if edge == '0' else intervals[path][0]
        return 0
    graph = []
    for i, (path, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            effect, targets = ['increment', arg], [after]
        elif op == 'CD':
            effect, targets = ['decrement', arg], [unwind(path, '0', 1), after]
        elif op == 'CB':
            effect, targets = ['identity'], [unwind(path, '0', arg)]
        elif op == 'CC':
            effect, targets = ['identity'], [unwind(path, '1', arg)]
        else:
            effect, targets = ['halt'], []
        graph.append([effect, targets])
    return graph


def subtree(root, path):
    for bit in path:
        require(not leaf(root), 'Stage path extends past a leaf')
        root = root[int(bit)]
    return root


def replace(root, path, node):
    if not path: return node
    bit = int(path[0]); children = list(root)
    children[bit] = replace(children[bit], path[1:], node)
    return tuple(children)


