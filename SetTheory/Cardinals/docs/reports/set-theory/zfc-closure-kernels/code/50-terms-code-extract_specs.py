#!/usr/bin/env python3
"""Extract the fixed prefix terms from the pinned ProveIt Code254 source.

This is an intentionally narrow syntax reader, not a Lean interpreter.
Its output is a finite term specification used by both reference checkers.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

ARITIES = dict(wim=2, wel=2, wal=2, weq=2, wn=1, wa=2, wex=2,
               rho1=2, rho2=3, rho3=3, rho4=3, rho5=3, rho6=2,
               rho7=3, rho8=4, bundleC=3, bundleG=3, bundle=3)
NAMES = ['rho1', 'rho2', 'rho3', 'rho4', 'rho5', 'rho6', 'rho7', 'rho8',
         'bundleC', 'bundleG', 'bundle']


def extract(source):
    result = {}
    for name in NAMES:
        pattern = (r'^def ' + name +
                   r' \(([^:]+): Nat\) : Nat :=\s*(.*?)'
                   r'(?=\n\n|\n(?:def|theorem|inductive) |\Z)')
        match = re.search(pattern, source, re.M | re.S)
        if match is None:
            raise ValueError('Missing fixed definition: ' + name)
        params = match[1].split()
        text = match[2]
        tokens = re.findall(r'[A-Za-z][A-Za-z0-9_]*|[()]|[0-9]+', text)
        residual = re.sub(r'[A-Za-z][A-Za-z0-9_]*|[()]|[0-9]+|\s+', '', text)
        if residual:
            raise ValueError('Unrecognized syntax: ' + residual)
        pos = 0

        def term():
            nonlocal pos
            token = tokens[pos]
            pos += 1
            if token == '(':
                ans = term()
                if tokens[pos] != ')':
                    raise ValueError('Expected closing parenthesis')
                pos += 1
                return ans
            if token in ARITIES:
                return [token] + [term() for _ in range(ARITIES[token])]
            if token in params or token == 'F':
                return token
            if token.isdigit():
                return int(token)
            raise ValueError('Unknown token: ' + token)

        body = term()
        if pos != len(tokens) or len(params) != ARITIES[name]:
            raise ValueError('Incomplete fixed term: ' + name)
        result[name] = {'parameters': params, 'term': body}
    return result


if __name__ == '__main__':
    source = Path(sys.argv[1]).read_bytes()
    output = {'source_sha256': hashlib.sha256(source).hexdigest(),
              'source_pin': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
              'definitions': extract(source.decode('utf-8'))}
    Path(sys.argv[2]).write_text(json.dumps(output, indent=2) + '\n')
