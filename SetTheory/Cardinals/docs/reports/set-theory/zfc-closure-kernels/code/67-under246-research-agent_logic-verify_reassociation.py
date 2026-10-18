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

RESEARCH = Path(__file__).resolve().parents[1]
BASE = RESEARCH / 'sources/beyond252/beyond252/exploratory/data/original203.json'
LITERAL = RESEARCH / 'sources/context246/zfc-context246/sources/Prog254.v'
LAYOUTS = RESEARCH / 'agent_audit/layout_search'
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


def audit(base, candidate, path, filehash):
    old_normal = base.normal(('N', base.root))
    new_normal = candidate.normal(('N', candidate.root))
    assert old_normal == new_normal, 'Complete ordered normal forms differ'
    old_graph, new_graph = base.graph(), candidate.graph()
    assert len(old_graph) == len(new_graph)
    for i, (a, b) in enumerate(zip(old_graph, new_graph)):
        assert a == b, (i, base.sites[i], candidate.sites[i], a, b)
    assert base.leaf('') == candidate.leaf('') == 0
    assert len(candidate.reached) == len(candidate.nodes), 'Unused stored node'
    return {
        'file': path.name,
        'file_sha256': filehash,
        'status': 'PASS',
        'nodes': len(candidate.nodes),
        'root': candidate.root,
        'metrics_root_zero_prefix_max_zero_depth_max_path_depth': candidate.metrics(),
        'root_escape_bounds': candidate.bounds(('N', candidate.root)),
        'leaf_count': len(new_graph),
        'guarded_cases_checked': sum(max(1, len(s)) for _, s in new_graph),
        'successor_edges_checked': sum(len(s) for _, s in new_graph),
        'halt_leaves': sum(e[0] == 'H' for e, _ in new_graph),
        'changed_leaf_paths': sum(a[0] != b[0] for a, b in zip(base.sites, candidate.sites)),
        'ordered_normal_form_sha256': sha(encode(new_normal)),
        'exact_guarded_leaf_cfg_sha256': sha(encode(new_graph)),
        'semantics': 'Same DFS-indexed instruction, guarded successor, and empty-path initial leaf; exact source-instruction bisimulation for all register valuations.'
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('candidates', nargs='*', type=Path)
    ap.add_argument('--baseline', type=Path, default=BASE)
    ap.add_argument('--literal', type=Path, default=LITERAL)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('reassociation_audit.json'))
    a = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must be enabled')
    nodes, root, basehash = read_json(a.baseline)
    base = Decoder(nodes, root)
    literal_nodes, literal_root = read_literal(a.literal)
    literal = Decoder(literal_nodes, literal_root)
    assert base.tree(('N', base.root)) == literal.tree(('N', literal.root))
    paths = a.candidates or [
        LAYOUTS / 'dictionary_max0_freq2.json',
        LAYOUTS / 'dictionary_max0_freq2_zero7_depth39_old1.json',
        LAYOUTS / 'dictionary_max20_freq2_zero7_depth39_old1.json',
    ]
    results = []
    for path in paths:
        cn, cr, ch = read_json(path)
        results.append(audit(base, Decoder(cn, cr), path, ch))
    # Independently check the concise raw-node identities reported by the search.
    assert nodes[73] == (('N', 47), ('N', 63))
    assert nodes[48] == (('N', 39), ('N', 47))
    raw202 = dict(nodes)
    raw202[74] = (('N', 48), ('N', 63))
    del raw202[73]
    d202 = Decoder(raw202, root)
    assert d202.graph() == base.graph()
    assert d202.normal(('N', root)) == base.normal(('N', root))
    assert len(d202.reached) == 202
    raw201 = dict(nodes)
    fresh = max(nodes) + 1
    raw201[fresh] = (('N', 48), ('N', 79))
    raw201[99] = (('N', 43), ('N', fresh))
    raw201[59] = (('N', 99), ('I', 1))
    raw201[74] = (('N', 48), ('N', 63))
    raw201[83] = (('N', 63), ('N', fresh))
    for old in (49, 73, 82):
        del raw201[old]
    d201 = Decoder(raw201, root)
    assert d201.graph() == base.graph()
    assert d201.normal(('N', root)) == base.normal(('N', root))
    assert len(d201.reached) == 201
    concise_emission_match = None
    for path in paths:
        if path.name == 'dictionary_max20_freq2_zero7_depth39_old1.json':
            last_nodes, last_root, _ = read_json(path)
            assert d201.tree(('N', root)) == Decoder(last_nodes, last_root).tree(('N', last_root))
            concise_emission_match = True
    assert all(base.bounds(('N', i)) == (0, 0) for i in (39, 47, 63, 43, 57))
    output = {
        'status': 'PASS',
        'baseline_file_sha256': basehash,
        'literal_source_sha256': EXPECTED_LITERAL_HASH,
        'baseline_nodes': len(nodes),
        'baseline_literal_unfolding_identical': True,
        'baseline_metrics': base.metrics(),
        'concise_202_rewrite_checked': True,
        'concise_201_rewrite_checked': True,
        'concise_201_emitted_tree_match': concise_emission_match,
        'closed_old_nodes_for_202_rotation': {i: base.bounds(('N', i)) for i in (39, 47, 63)},
        'closed_old_components_for_201_rewrite': {i: base.bounds(('N', i)) for i in (39, 47, 63, 43, 57)},
        'results': results,
        'scope': 'Source DAG equivalence only; no binary table compiler, context fold, register macro, bootstrap or working-state count is certified.'
    }
    a.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
