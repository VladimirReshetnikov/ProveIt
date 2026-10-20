#!/usr/bin/env python3
"""Reconstruct the recorded finite search outputs; no discovery search runs."""
from pathlib import Path
from functools import cache
import argparse
import gzip
import hashlib
import importlib.util
import json
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Assertions required')
    require(not args.output.exists(), 'Use a fresh output directory')
    provenance = json.loads((HERE / 'provenance.json').read_text())
    for name, digest in provenance['inputs'].items():
        require(sha((ROOT / name).read_bytes()) == digest, ('Input drift', name))
    base = gzip.decompress((HERE / 'results/intermediate-nodes.txt.gz').read_bytes())
    roots = []
    for run in provenance['runs']:
        tail = (HERE / 'results' / (run['name'] + '.roots.txt')).read_bytes()
        require(sha(base + tail) == run['nodes_sha256'], 'Node-stream reconstruction')
        require(len(tail.splitlines()) == run['roots'], 'Root count')
        require(sha((HERE / run['search_source']).read_bytes()) == run['search_source_sha256'], 'Search source drift')
        roots.extend(tuple(map(int, line.split()[1:3])) for line in tail.splitlines())
    require(len(roots) == len(set(roots)) == 263, 'Distinct recovered roots')
    nodes = list(map(freeze, json.loads((HERE / 'atoms.json').read_text())))
    for line in base.splitlines():
        i, left, right, cost = map(int, line.split())
        require(i == len(nodes) and left < i and right < i and 1 <= cost <= 5, 'Node order')
        nodes.append((nodes[left], nodes[right]))
    require(len(nodes) == 377821, 'Intermediate census')

    sys.dont_write_bytecode = True
    sys.path.insert(0, str(HERE.parent / 'k219-continuation-search/compiler-inputs'))
    import source_language as source
    verifier = ROOT / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/140-k219-res-enc-verify_clean_eq.py'
    spec = importlib.util.spec_from_file_location('finite_verifier', verifier)
    check = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(check)
    accepted = HERE.parent / 'candidate-k219'
    old = freeze(json.loads((accepted / 'new_equality_macro.json').read_text()))
    tree = source.tree(json.loads((accepted / 'sites219.json').read_text()))

    @cache
    def replace(node, macro):
        if node == old:
            return macro, 1
        if source.leaf(node):
            return node, 0
        left, a = replace(node[0], macro)
        right, b = replace(node[1], macro)
        return (left, right), a + b

    cases = [(a, b) for a in range(16) for b in range(16)]
    cases += [(0, 100), (100, 0), (100, 100), (99, 100), (100, 99)]
    expected = json.loads((HERE / 'results/analysis.json').read_text())['results']
    args.output.mkdir(parents=True)
    results = []
    start = time.monotonic()
    for i, (a, b) in enumerate(roots):
        macro = nodes[a], nodes[b]
        new, count = replace(tree, macro)
        require(count == 4, 'Exact four replacements')
        rows = source.sites(new)
        require(source.graph_arithmetic(rows)[0] == source.graph_intervals(rows), 'Independent whole-source CFGs')
        result = {'id': i, 'root': [a, b], 'metrics': source.metrics(new),
                  'macro': macro, 'macro_leaves': len(source.sites(macro)),
                  'right_decrements': sum(op == 'CD' and path[-1] == '1' for path, op, arg in rows),
                  'right_increments': sorted({arg for path, op, arg in source.sites(macro) if op == 'CI' and path[-1] == '1'})}
        ca = cb = None
        try:
            graph = check.compile_cfg(((macro, ('CI', 0)), ('CH', None)))
            total = 0
            for ca, cb in cases:
                total += check.run(graph, ca, cb)
            result.update(finite='PASS', cases=len(cases), steps=total)
        except (AssertionError, ValueError, IndexError) as error:
            result.update(finite='FAIL', failure=str(error), pair=[ca, cb])
        require(json.loads(json.dumps(result)) == expected[i], ('Recorded diagnostic changed', i))
        results.append(result)
        if result['metrics']['dag_nodes'] == 207 and result['finite'] == 'PASS':
            (args.output / f'candidate-{i:03d}.sites.json').write_bytes(source.compact(rows))
    require(len(results) == 263, 'Complete diagnostic coverage')
    receipt = {'status': 'RECONSTRUCTION_AND_FINITE_DIAGNOSTICS_PASS',
               'macros': len(results), 'finite_pass': sum(r['finite'] == 'PASS' for r in results),
               'finite_fail': sum(r['finite'] == 'FAIL' for r in results),
               'minimum_dag': min(r['metrics']['dag_nodes'] for r in results),
               'seconds': time.monotonic() - start, 'script_sha256': sha(Path(__file__).read_bytes()),
               'scope': 'Exact recorded streams, substitutions, CFGs and finite diagnostics only; no unbounded contract, runtime or minimality theorem.'}
    (args.output / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
