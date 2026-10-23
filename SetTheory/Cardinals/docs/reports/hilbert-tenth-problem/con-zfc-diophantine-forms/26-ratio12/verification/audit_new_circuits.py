#!/usr/bin/env python3
"""Independent structural/degree audit; imports no candidate generator.

This checks finite circuit properties only. The accompanying independent
mathematical reviews state the unbounded semantic reasoning and dependencies.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(path):
    packet = json.loads(path.read_text())
    source = packet['source']
    inputs = packet['witnesses']
    constants = packet['fixed_numerals']
    names = set(inputs + constants)
    require(len(names) == len(inputs) + len(constants), 'duplicate input')
    degrees = {n: 1 for n in inputs}
    degrees.update({n: 0 for n in constants})
    outputs = packet.get('comparisons') or [[packet['output'], 0]]
    for name, op, x, y in source:
        require(name not in names, 'duplicate gate ' + name)
        require(op in ('+', '-', '*'), 'unsupported operation')
        for v in (x, y):
            require(isinstance(v, int) or v in names, 'missing operand ' + str(v))
        dx, dy = (0 if isinstance(v, int) else degrees[v] for v in (x, y))
        degrees[name] = dx + dy if op == '*' else max(dx, dy)
        names.add(name)
    live = {x for pair in outputs for x in pair if isinstance(x, str)}
    for name, op, x, y in reversed(source):
        require(name in live, 'dead gate ' + name)
        live.update(v for v in (x, y) if isinstance(v, str))
    require(set(inputs + constants) <= live, 'dead input')
    result = {
        'path': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'unknowns': len(inputs), 'operations': len(source),
        'multiplications': sum(row[1] == '*' for row in source),
        'additions_subtractions': sum(row[1] != '*' for row in source),
        'all_gates_live': True, 'all_inputs_live': True,
        'syntactic_residual_degree_upper_bounds': [
            max(0 if isinstance(x, int) else degrees[x] for x in pair)
            for pair in outputs
        ],
    }
    return result


def main():
    paths = sorted((ROOT/'arithmetic').glob('integer24*.json'))
    paths += sorted((ROOT/'arithmetic').glob('ratio12*.json'))
    results = []
    for path in paths:
        if 'source' in json.loads(path.read_text()):
            results.append(audit(path))
    baseline = json.loads((ROOT/'references'/'21-norm12'/'arithmetic'/'norm12_product.json').read_text())
    candidate = json.loads((ROOT/'arithmetic'/'integer24_product.json').read_text())
    require(candidate['source'][47:] == baseline['source'], '24 core changed')
    receipt = {
        'packets': results,
        'integer24_product_suffix_identical_to_independently_fetched_package21': True,
        'scope': 'Exact circuit structure, counts, liveness, and syntactic degree upper bounds; semantic proof is in the independent review notes.',
    }
    (HERE/'INDEPENDENT_CIRCUIT_CHECKS.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
