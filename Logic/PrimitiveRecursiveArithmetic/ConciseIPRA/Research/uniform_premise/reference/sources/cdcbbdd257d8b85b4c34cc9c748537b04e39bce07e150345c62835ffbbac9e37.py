"""Reproduce driver-only controls from exact frozen upstream source bytes.

Only a top-level bare except handler consisting of print('REJECT') and
a bare re-raise is removed. Its try body replaces the wrapper. No inference,
substitution, parser, data representation or acceptance code changes.
"""
import ast
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def remove_wrapper(source):
    tree = ast.parse(source)
    wrappers = [node for node in tree.body if isinstance(node, ast.Try)]
    if len(wrappers) != 1:
        raise ValueError('Expected one top-level try wrapper')
    wrapper, = wrappers
    if wrapper.orelse or wrapper.finalbody or len(wrapper.handlers) != 1:
        raise ValueError('Unexpected wrapper structure')
    handler, = wrapper.handlers
    if handler.type is not None or handler.name is not None:
        raise ValueError('Expected bare except')
    if (len(handler.body) != 2
            or ast.unparse(handler.body[0]) != "print('REJECT')"
            or not isinstance(handler.body[1], ast.Raise)
            or handler.body[1].exc is not None
            or handler.body[1].cause is not None):
        raise ValueError('Handler does more than print and re-raise')
    tree.body = [child for node in tree.body
                 for child in (node.body if node is wrapper else [node])]
    return (ast.unparse(tree) + '\n').encode('utf-8')


def main():
    rows = json.loads((ROOT / 'metrics.json').read_text())
    for row in rows:
        source = (ROOT / row['frozen_original']).read_bytes()
        if hashlib.sha256(source).hexdigest() != row['old']['sha256']:
            raise ValueError('Frozen original source changed')
        result = remove_wrapper(source.decode('utf-8'))
        if hashlib.sha256(result).hexdigest() != row['new']['sha256']:
            raise ValueError('Matched control differs from recorded transformation')
        output = ROOT / row['matched_file']
        output.write_bytes(result)
        output.with_suffix('.py.gz').write_bytes(
            gzip.compress(result, compresslevel=9, mtime=0))
    print('Reproduced', len(rows), 'exact driver-only matched controls.')


if __name__ == '__main__':
    main()
