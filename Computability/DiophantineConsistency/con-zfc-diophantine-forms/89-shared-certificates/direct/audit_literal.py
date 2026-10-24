#!/usr/bin/env python3
"""Reproduce the finite literal-C222 DAG comparison receipt.

There are 300 fixed-seed assignments, each evaluated modulo three distinct
primes: 900 comparisons in total. The reference evaluator reads the pinned
expanded branch definitions and does not call direct_calculus.py.
The exact compositional code identities are checked by audit_calculus.py.
"""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
from random import Random
import sys


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path, default=here/'affine_shared_step.json')
    parser.add_argument('--source', type=Path, default=here/'wire_eliminated_source.json')
    parser.add_argument('--builder', type=Path, default=here/'build_equation.py')
    parser.add_argument('--output', type=Path, default=here/'LITERAL_AUDIT.json')
    args = parser.parse_args()
    sys.path.insert(0, str(args.builder.resolve().parent))
    from audit_source import require, circuit_value, reduced_value
    from direct_calculus import source_pair_calculus
    spec = importlib.util.spec_from_file_location('literal_audit_builder', args.builder)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    original = json.loads(args.original.read_text())
    source = json.loads(args.source.read_text())
    builder = module.Builder()
    names = ['x', 'y', 'm', 'M0', 'p', 'q', 'v', 'a', 'b', 'c', 'd',
             'S', 'Sp', 'u', 'r', 'vq', 'rp']
    nodes = {name: builder.new(name) for name in names}
    index = builder.new('i')
    pair = source_pair_calculus(builder, source, nodes, index, False)
    rng = Random(829710)
    primes = [1000003, 1000033, 1000037]
    comparisons = 0
    for _ in range(300):
        env = {name: rng.randrange(12) for name in names}
        row_index = rng.randrange(6)
        inputs = {nodes[name][1]: env[name] for name in names}
        inputs[index[1]] = row_index
        for prime in primes:
            actual = circuit_value(builder, pair, inputs, prime)
            expected = reduced_value(original, env, row_index, prime)
            require(actual == expected, 'literal calculus DAG differs from pinned branch source')
            comparisons += 1
    require(comparisons == 900, 'unexpected comparison count')
    payload = {
        'status': 'PASS',
        'method': 'independent expanded-source evaluation versus literal calculus DAG',
        'assignment_count': 300,
        'finite_comparisons': comparisons,
        'seed': 829710,
        'primes': primes,
        'source_dag_nodes': len(builder.gates),
        'optimized_python': not __debug__,
        'sha256': {
            'audit_literal.py': sha256(Path(__file__).read_bytes()).hexdigest(),
            'audit_source.py': sha256((here/'audit_source.py').read_bytes()).hexdigest(),
            'direct_calculus.py': sha256((args.builder.parent/'direct_calculus.py').read_bytes()).hexdigest(),
            'build_equation.py': sha256(args.builder.read_bytes()).hexdigest(),
            'affine_shared_step.json': sha256(args.original.read_bytes()).hexdigest(),
            'wire_eliminated_source.json': sha256(args.source.read_bytes()).hexdigest(),
        },
        'scope': 'Finite regression controls; exact code identities are checked separately by audit_calculus.py.'
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True)+'\n')
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
