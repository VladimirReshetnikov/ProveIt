#!/usr/bin/env python3
"""Exact source-level sharing for KSource215Data's two expanded trees.

This is a prototype source transformation, NOT a Lean kernel verification.
Usage: python3 compact_source_trees.py INPUT.lean OUTPUT_DIRECTORY
The resulting file keeps every public definition/theorem and the full original
certificate. The two Tree literals are replaced by a common, acyclic table of
private Tree definitions. An independently written output parser unfolds every
emitted definition and requires exact equality with both input abstract trees.
No hash equality is used as a proxy for tree equality.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


class LiteralParser:
    def __init__(self, source):
        self.tokens = re.findall(r'\(|\)|\.[A-Za-z]+|[0-9]+', source)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', source), 'unrecognized input text'
        self.i = 0

    def take(self, expected=None):
        value = self.tokens[self.i]
        self.i += 1
        if expected is not None:
            assert value == expected, (value, expected)
        return value

    def tree(self):
        self.take('(')
        kind = self.take()
        if kind == '.node':
            result = ('node', self.tree(), self.tree())
        else:
            assert kind == '.leaf'
            bracket = self.tokens[self.i] == '('
            if bracket:
                self.take('(')
            op = self.take()[1:]
            assert op in {'inc', 'decnz', 'brk', 'cont', 'halt'}
            arg = None if op == 'halt' else int(self.take())
            if bracket:
                self.take(')')
            result = ('leaf', op, arg)
        self.take(')')
        return result

    def parse(self):
        tree = self.tree()
        assert self.i == len(self.tokens)
        return tree


def tree_stats(root):
    unique = set()
    def visit(node):
        unique.add(node)
        if node[0] == 'leaf':
            return 1, 0
        l, lh = visit(node[1])
        r, rh = visit(node[2])
        return l + r, max(lh, rh) + 1
    leaves, height = visit(root)
    return {'leaves': leaves, 'height': height, 'distinct_subtrees': len(unique),
            'distinct_internal_nodes': sum(x[0] == 'node' for x in unique)}


def decode_generated(block):
    """Independent line parser of emitted definitions; all references go backward."""
    values = {}
    public = {}
    for line in block.splitlines():
        line = line.strip()
        m = re.fullmatch(r'private def (k215SharedTree[0-9]+) : Tree := (.*)', line)
        if m:
            name, expression = m.groups()
            assert name not in values
            node = re.fullmatch(r'\.node (k215SharedTree[0-9]+) (k215SharedTree[0-9]+)', expression)
            leaf = re.fullmatch(r'\.leaf \(\.(inc|decnz|brk|cont) ([0-9]+)\)', expression)
            if node:
                values[name] = ('node', values[node[1]], values[node[2]])
            elif leaf:
                values[name] = ('leaf', leaf[1], int(leaf[2]))
            else:
                assert expression == '.leaf .halt', expression
                values[name] = ('leaf', 'halt', None)
        else:
            m = re.fullmatch(r'def (t215|tD) : Tree := (k215SharedTree[0-9]+)', line)
            if m:
                public[m[1]] = values[m[2]]
            else:
                assert not line or line.startswith(('/--', '--')), line
    assert set(public) == {'t215', 'tD'}
    return public, len(values)


def compact(source):
    roots = {}
    for name in ('t215', 'tD'):
        match = re.search(r'def '+name+r' : Tree :=\n(.*?)\n\n', source, re.S)
        assert match, name
        roots[name] = LiteralParser(match[1]).parse()
    nodes, index = [], {}
    def intern(node):
        if node not in index:
            if node[0] == 'node':
                intern(node[1]); intern(node[2])
            index[node] = len(nodes)
            nodes.append(node)
        return index[node]
    for root in roots.values():
        intern(root)
    def name(node):
        return 'k215SharedTree'+str(index[node]).zfill(3)
    lines = ['/-- Exact shared representation of the two original Tree literals. -/']
    for node in nodes:
        if node[0] == 'node':
            rhs = f'.node {name(node[1])} {name(node[2])}'
        elif node[1] == 'halt':
            rhs = '.leaf .halt'
        else:
            rhs = f'.leaf (.{node[1]} {node[2]})'
        lines.append(f'private def {name(node)} : Tree := {rhs}')
    lines += ['', '/-- The exact decoder tree of the 215-state machine. -/',
              f'def t215 : Tree := {name(roots["t215"])}', '',
              '/-- The exact decoder tree of dagPerm. -/',
              f'def tD : Tree := {name(roots["tD"])}', '']
    block = '\n'.join(lines)+'\n'
    decoded, count = decode_generated(block)
    assert decoded == roots, 'generated abstract syntax differs'
    start = source.index('/-- The 215\'s decoder tree, written out. -/')
    end = source.index('theorem t215_eq :', start)
    original_block = source[start:end]
    result = source[:start]+block+source[end:]
    assert result[result.index('theorem t215_eq :'):] == source[end:]
    metadata = {
        'status': 'PASS_EXACT_AST_ROUNDTRIP_NOT_KERNEL_COMPILED',
        'kernel_compiled': False,
        'input_sha256': sha(source.encode()), 'output_sha256': sha(result.encode()),
        'input_bytes': len(source.encode()), 'output_bytes': len(result.encode()),
        'saved_bytes': len(source.encode())-len(result.encode()),
        'original_tree_block_bytes': len(original_block.encode()),
        'shared_tree_block_bytes': len(block.encode()),
        'shared_definitions': count,
        'roots': {key: tree_stats(value) for key,value in roots.items()},
        'checks': ['exact input AST equals fully unfolded output AST for each root',
                   'all shared references point to earlier declarations',
                   'all public definitions and theorem statements retained',
                   'entire certificate and suffix from theorem t215_eq retained byte-for-byte',
                   'all source before the two tree definitions retained byte-for-byte'],
        'remaining_gate': 'Rebuild KSource215Data and all affected endpoint consumers with pinned Lean; compare endpoint axioms and timings.'
    }
    return result, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    source = args.input.read_text()
    result, metadata = compact(source)
    args.output_directory.mkdir(parents=True, exist_ok=True)
    output = args.output_directory/'KSource215Data.lean'
    output.write_text(result)
    (args.output_directory/'compact_trees_result.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))


if __name__ == '__main__':
    main()
