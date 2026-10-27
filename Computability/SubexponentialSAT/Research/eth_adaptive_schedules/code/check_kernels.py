"""Exact equivalence checks against pinned reference implementations."""
import argparse
from dataclasses import asdict
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
import json
import hashlib
from pathlib import Path
import random
import sys
import time

HERE = Path(__file__).resolve().parent
REFERENCE = HERE / 'reference'
sys.path.insert(0, str(HERE))
from incremental_packing import derandomize_incremental, derandomize_integer
from incremental_matching import label_graph_incremental

def load(name, path):
    spec = spec_from_file_location(name, path)
    mod = module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

for entry in json.loads((REFERENCE / 'provenance.json').read_text()):
    raw = (HERE / entry['local_file']).read_bytes()
    if hashlib.sha256(raw).hexdigest() != entry['sha256']:
        raise ValueError('Reference checksum mismatch: ' + entry['local_file'])

col = load('reference_columns', REFERENCE / 'balanced_columns.py')
matching = load('reference_matching', REFERENCE / 'matching.py')


def check_columns():
    count = candidates = 0
    cases = []
    for groups, columns in [(1, 0), (1, 3), (2, 2), (2, 3), (3, 2)]:
        for flat in product(range(2), repeat=groups * columns):
            weights = [list(flat[r*columns:(r+1)*columns]) for r in range(groups)]
            cases.append((weights, groups))
    rng = random.Random(20261026)
    for _ in range(80):
        groups, columns = rng.randrange(1, 7), rng.randrange(0, 13)
        cases.append(([[rng.randrange(4) for _ in range(columns)] for _ in range(groups)], groups))
    for weights, groups in cases:
        for z in [F(3, 2), F(17, 16)]:
            for threshold in [0, sum(map(sum, weights)) + 4 * groups + 1]:
                expected = asdict(col.derandomize_columns(weights, groups, z, threshold))
                for implementation in [derandomize_incremental, derandomize_integer]:
                    got = asdict(implementation(weights, groups, z, threshold))
                    if got != expected:
                        raise AssertionError((implementation.__name__, weights, z, threshold))
                count += 1
                candidates += len(weights[0]) * groups
    invalid = [([], 0, F(3,2), 1), ([[1], [1,2]], 2, F(3,2), 1),
               ([[-1]], 1, F(3,2), 1), ([[1]], 1, F(1), 1), ([[1]], 1, F(3,2), -1)]
    for args in invalid:
        for implementation in [derandomize_incremental, derandomize_integer]:
            try: implementation(*args)
            except ValueError: pass
            else: raise AssertionError('Invalid input accepted')
    return {'instances': count, 'candidate_potentials_per_implementation': candidates,
            'implementations': 2, 'invalid_cases_per_implementation': len(invalid)}


def check_matching():
    count = trace_values = 0
    edge_slots = [(i, j) for i in range(2) for j in range(3)]
    cases = [[edge for edge, present in zip(edge_slots, bits) if present]
             for bits in product(range(2), repeat=len(edge_slots))]
    rng = random.Random(20261027)
    for _ in range(60):
        cases.append([(rng.randrange(4), rng.randrange(4)) for _ in range(rng.randrange(15))])
    cases += [[(0,0)] * k for k in range(1, 8)]
    cases += [[[0, 0], [0, 1], [1, 1]], [[0, 0], [0, 0]]]
    for edges in cases:
        for labels, lam in [(1, 1), (2, 3), (3, 4)]:
            expected = matching.label_graph(edges, labels, lam)
            actual = label_graph_incremental(edges, labels, lam)
            if actual != expected:
                raise AssertionError((edges, labels, lam))
            count += 1
            trace_values += len(actual['trace'])
    return {'instances': count, 'exact_trace_values': trace_values,
            'all_assignments_loads_matchings_thresholds_and_potentials_identical': True}

def check_independent_expectation():
    # Enumerate all completions, then evaluate the defining exponential of
    # final cell loads. This uses neither implementation's product formula.
    slots = [(i,j) for i in range(2) for j in range(2)]
    prefix_checks = completion_evaluations = 0
    for bits in product(range(2), repeat=4):
        edges = [edge for edge, bit in zip(slots, bits) if bit]
        for labels, lam in [(2,3),(3,2)]:
            result = label_graph_incremental(edges, labels, lam)
            groups = result['groups']
            vertices = sorted(result['assignment'])
            target_values = [result['initial']] + result['trace']
            t = F(lam+1,lam)
            for prefix in range(len(vertices)+1):
                fixed = {v:result['assignment'][v] for v in vertices[:prefix]}
                remaining = vertices[prefix:]
                value_sum = F(0)
                for completion in product(range(labels), repeat=len(remaining)):
                    assignment = {**fixed, **dict(zip(remaining, completion))}
                    exact = F(0)
                    for group, threshold in zip(groups, result['thresholds']):
                        cells = [[0]*labels for _ in range(labels)]
                        for left,right in group:
                            cells[assignment['L',left]][assignment['R',right]] += 1
                        exact += sum((t**(load-threshold) for row in cells for load in row), F(0))
                    value_sum += exact
                    completion_evaluations += 1
                expected = value_sum / (labels ** len(remaining))
                if expected != target_values[prefix]:
                    raise AssertionError(('independent expectation', edges, labels, prefix))
                prefix_checks += 1
    return {'prefix_expectations_checked':prefix_checks,
            'full_assignment_potential_evaluations':completion_evaluations,
            'all_exact': True}

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=HERE / 'checks.json')
    args = parser.parse_args()
    start = time.perf_counter()
    result = {'columns': check_columns(), 'matching': check_matching(), 'independent_expectation': check_independent_expectation(),
              'python': sys.version, 'elapsed_seconds': time.perf_counter() - start,
              'optimized_python': not __debug__}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
