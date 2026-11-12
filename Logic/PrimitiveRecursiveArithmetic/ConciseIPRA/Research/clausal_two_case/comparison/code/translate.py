"""Untrusted, independently checked elimination of the root Eval row.

Both kernels verify the end sequent. At every transformed node we compare
its derived formula under exactly the same local context and fresh scope.
This translator is not imported by the standalone acceptance module.
"""
import copy
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
CONTROL = ROOT / 'code' / 'control.py'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

old = load('ce5_original', CONTROL)
new = load('ce5_two_case', ROOT / 'code' / 'checker.py')


def nodes(proof):
    tag = proof[0]
    if tag == 'r':
        return 1
    if tag in ('u', 'i'):
        return 1 + nodes(proof[3])
    if tag == 'e':
        return 1 + nodes(proof[2]) + nodes(proof[3])
    if tag == 'v':
        return 1 + nodes(proof[1]) + nodes(proof[2])
    raise ValueError('unknown proof node')


def transform(proof, context, scope):
    """Return (new proof, number of eliminated root applications)."""
    source_formula = old.derive(proof, context, scope)
    tag = proof[0]
    roots = 0
    if tag == 'r':
        result = copy.deepcopy(proof)
    elif tag == 'u':
        child, roots = transform(proof[3], context, scope)
        result = ['u', proof[1], copy.deepcopy(proof[2]), child]
    elif tag == 'v':
        major, k1 = transform(proof[1], context, scope)
        minor, k2 = transform(proof[2], context, scope)
        roots = k1 + k2
        s, t = old.derive(proof[1], context, scope)
        b, r = old.derive(proof[2], context, scope)
        if b == s:
            frame = [0, copy.deepcopy(s), 0]
            result = ['v', major, ['v', minor, ['r', frame]]]
            roots += 1
        else:
            result = ['v', major, minor]
    elif tag in ('e', 'i'):
        goal, data, branch = proof[1:]
        fresh = -scope - 1
        if tag == 'e':
            major, roots = transform(data, context, scope)
            paired = old.derive(data, context, scope)
            body = old.opening(paired[0], fresh, 1)
            clause = (old.opening(body, 0), body)
            transformed_data = major
        else:
            body = old.opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], old.opening(body, eta))
            transformed_data = copy.deepcopy(data)
        child, branch_roots = transform(branch, context + [clause], scope + 1)
        roots += branch_roots
        result = [tag, copy.deepcopy(goal), transformed_data, child]
    else:
        raise ValueError('unknown proof rule')
    if new.derive(result, context, scope) != source_formula:
        raise RuntimeError('node translation changed formula')
    if nodes(result) != nodes(proof) + 2 * roots:
        raise RuntimeError('exact proof-node identity failed')
    return result, roots


def translate(data):
    old.verify(data)
    proof, roots = transform(data['proof'], [], 0)
    result = {'goal': copy.deepcopy(data['goal']), 'proof': proof}
    new.verify(result)
    old.verify(result)  # Inclusion is checked too.
    stats = {'old_nodes': nodes(data['proof']), 'root_nodes': roots,
             'new_nodes': nodes(proof)}
    return result, stats


if __name__ == '__main__':
    output, stats = translate(json.load(sys.stdin))
    print(json.dumps(output, separators=(',', ':')))
    print(json.dumps(stats), file=sys.stderr)
