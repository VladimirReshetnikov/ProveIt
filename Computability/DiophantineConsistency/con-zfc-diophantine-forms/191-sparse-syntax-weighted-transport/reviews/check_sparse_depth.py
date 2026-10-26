#!/usr/bin/env python3
"""Depth audit of literal C222 schema functions without importing a compiler."""
import argparse
import ast
import hashlib
import json
from pathlib import Path


def require(c, message):
    if not c:
        raise ValueError(message)


def audit(path, function_name=None):
    raw = path.read_bytes()
    module = ast.parse(raw.decode())
    choices = {function_name} if function_name else {'direct_source', 'generate'}
    outer = [n for n in module.body if isinstance(n, ast.FunctionDef)
             and n.name in choices]
    require(len(outer) == 1, 'Expected one source schema function')
    retained = []
    names = {'N', 'X', 'req', 'clos', 'bundle'}
    seen = set()
    for n in outer[0].body:
        if isinstance(n, ast.FunctionDef) and n.name in names:
            retained.append(n)
            seen.add(n.name)
        if isinstance(n, ast.Assign) and len(n.targets) == 1 \
                and isinstance(n.targets[0], ast.Name) \
                and n.targets[0].id == 'codes':
            retained.append(n)
    require(seen == names and len(retained) == 6, 'Missing literal schemas')
    selected = ast.Module(body=retained, type_ignores=[])
    # Only the displayed first-order constructor expressions are evaluated.
    # Imports, builder code, source-file reads, compilation and writes are absent.
    allowed_calls = names | {'I', 'M', 'A', 'E', 'const'}
    for n in ast.walk(selected):
        require(not isinstance(n, (ast.Import, ast.ImportFrom, ast.Attribute,
                                  ast.Global, ast.Nonlocal, ast.With,
                                  ast.For, ast.While, ast.Lambda)),
                'Unexpected operation in a literal schema')
        if isinstance(n, ast.Call):
            require(isinstance(n.func, ast.Name)
                    and n.func.id in allowed_calls,
                    'Unexpected call in a literal schema')
    ns = {'__builtins__': {}, 'ONE': 0, 'const': lambda unused: 0}
    for name in ['a', 'b', 'beta', 'c_b', 'c', 'd', 'p', 'q', 'v']:
        ns[name] = 0
    for name in ['I', 'M', 'A', 'E']:
        ns[name] = lambda x, y: 1 + max(x, y)
    exec(compile(selected, str(path), 'exec'), ns)
    expected = [4, 3, 3, 3, 3, 5, 4, 3, 19]
    require(ns['codes'] == expected, 'Unexpected constructor depths')
    return {'source_name': path.name,
            'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'axiom_depths': ns['codes']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='+', type=Path,
                        help='One or more literal source/producer Python files; paths are explicit for portable offline replay')
    parser.add_argument('--function', default=None,
                        help='Optional containing function name; default recognizes direct_source or generate')
    args = parser.parse_args()
    results = [audit(path, args.function) for path in args.sources]
    ordinary_code_bound = 2**(5+1)-1
    bundle_code_bound = 2**(19+1)-1
    axis_square_bound = 2*(1+8*(ordinary_code_bound+3)+10+7)
    joint_bound = 2*(bundle_code_bound+3)+1
    final_bound = axis_square_bound+joint_bound+1
    require(final_bound == 2098250 < 2**23, 'Local exponent arithmetic')
    print(json.dumps({
        'status': 'PASS',
        'method': 'Literal schema AST evaluated in constructor-depth algebra; no compiler import',
        'sources': results,
        'ordinary_label_exponent': ordinary_code_bound,
        'bundle_label_exponent': bundle_code_bound,
        'axis_square_exponent': axis_square_bound,
        'joint_exponent': joint_bound,
        'local_exponent': final_bound,
        'retained_local_budget': 2**23,
        'unbounded_hypotheses': 'R>=16; every local atom is nonnegative and <R',
        'proof': 'SPARSE_LOCAL_BOUND_REVIEW.md',
    }, indent=2))


if __name__ == '__main__':
    main()
