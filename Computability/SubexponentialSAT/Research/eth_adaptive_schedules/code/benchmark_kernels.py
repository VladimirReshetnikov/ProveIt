"""Reproducible single-process kernel benchmarks; no SAT runtime claims."""
import argparse
from dataclasses import asdict
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
import json
import hashlib
from pathlib import Path
import platform
import random
import statistics
import sys
import time

HERE = Path(__file__).resolve().parent
REFERENCE = HERE / 'reference'
sys.path.insert(0, str(HERE))
from incremental_packing import derandomize_integer
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

matching = load('benchmark_reference_matching', REFERENCE / 'matching.py')
suffix = load('benchmark_reference_suffix', REFERENCE / 'cached_suffix.py')


def integer_column_wrapper(n_rows, n_columns, edges, q, lambda_):
    """Same graph preprocessing and output fields as the suffix reference."""
    edges = tuple(edges)
    row_degrees, column_degrees = [0] * n_rows, [0] * n_columns
    for row, column in edges:
        if not 0 <= row < n_rows or not 0 <= column < n_columns:
            raise ValueError('invalid endpoint')
        row_degrees[row] += 1
        column_degrees[column] += 1
    delta = max([1, *row_degrees, *column_degrees])
    row_bin_weights, row_labels = [0] * q, []
    for degree in row_degrees:
        label = min(range(q), key=lambda a: (row_bin_weights[a], a))
        row_labels.append(label)
        row_bin_weights[label] += degree
    weights = [[0] * n_columns for _ in range(q)]
    for row, column in edges:
        weights[row_labels[row]][column] += 1
    z = F(delta * lambda_ + 1, delta * lambda_)
    result = derandomize_integer(weights, q, z, 0)
    return suffix.Labeling(n_rows, n_columns, edges, q, lambda_, delta,
                          tuple(row_labels), result.column_labels, tuple(row_bin_weights),
                          result.cell_loads, z,
                          (result.initial_potential,) + tuple(step.after for step in result.steps))


def compare(baseline, improved, arguments, repetitions):
    left, right = baseline(*arguments), improved(*arguments)
    if left != right:
        raise AssertionError('Outputs differ before benchmark')
    samples = {'baseline': [], 'improved': []}
    for rep in range(repetitions):
        order = [('baseline', baseline), ('improved', improved)]
        if rep % 2: order.reverse()
        for label, implementation in order:
            start = time.perf_counter_ns()
            result = implementation(*arguments)
            elapsed = (time.perf_counter_ns() - start) * 1e-9
            if result != left:
                raise AssertionError('Benchmark output changed')
            samples[label].append(elapsed)
    old = statistics.median(samples['baseline'])
    new = statistics.median(samples['improved'])
    return {'baseline_median_seconds': old, 'improved_median_seconds': new,
            'speedup_ratio': old / new, 'samples_seconds': samples,
            'outputs_identical': True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repetitions', type=int, default=5)
    parser.add_argument('--output', type=Path, default=HERE / 'benchmarks.json')
    args = parser.parse_args()
    result = {'scope': 'Exact graph-packing kernels only; no SAT instances or end-to-end solver.',
              'python': sys.version, 'platform': platform.platform(),
              'source_sha256': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
                                for name in ['incremental_matching.py', 'incremental_packing.py', 'benchmark_kernels.py']},
              'timing': 'perf_counter_ns, alternating run order, medians; output equality checked every run',
              'repetitions': args.repetitions, 'matching': [], 'cached_suffix_columns': []}
    for n, m, q in [(8, 16, 2), (16, 32, 4), (32, 64, 4), (64, 128, 4), (32, 96, 8)]:
        seed = 261000 + n * 100 + q
        rng = random.Random(seed)
        edges = [(rng.randrange(n//2), rng.randrange(n//2)) for _ in range(m)]
        row = {'incident_vertex_limit': n, 'edges': m, 'labels': q, 'lambda': 4, 'seed': seed}
        row.update(compare(matching.label_graph, label_graph_incremental, (edges, q, 4), args.repetitions))
        result['matching'].append(row)
        print(json.dumps({'matching': row}), flush=True)
    for n, m, q in [(16, 64, 4), (32, 128, 4), (64, 256, 8), (128, 512, 8), (256, 1024, 16)]:
        seed = 271000 + n * 100 + q
        rng = random.Random(seed)
        edges = [(rng.randrange(n//2), rng.randrange(n)) for _ in range(m)]
        row = {'row_vertices': n//2, 'column_vertices': n, 'edges': m, 'labels': q, 'lambda': 8, 'seed': seed}
        row.update(compare(suffix.deterministic_labeling, integer_column_wrapper,
                           (n//2, n, edges, q, 8), args.repetitions))
        result['cached_suffix_columns'].append(row)
        print(json.dumps({'cached_suffix_columns': row}), flush=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')

if __name__ == '__main__':
    main()
