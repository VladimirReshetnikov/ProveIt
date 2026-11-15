#!/usr/bin/env python3
"""Iterate finite noncircular folds, recording the explicit exploration boundary.

Requires a locally compiled ./noncircular and ../../comparison/census.py.
The canonicalization fixes native start74. Inputs and outputs which remove that
label are outside this particular closure driver and are counted explicitly.
"""
import argparse
from collections import Counter, deque
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('history_census', HERE.parents[1]/'comparison'/'census.py')
C = importlib.util.module_from_spec(spec)
spec.loader.exec_module(C)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('name')
    ap.add_argument('--radius', type=int, default=7)
    ap.add_argument('--fuel', type=int, default=31)
    ap.add_argument('--max-nodes', type=int, default=5000)
    ap.add_argument('--strategy', choices=['bfs', 'dfs'], default='bfs')
    ap.add_argument('--output', type=Path, help='Fresh output directory; default reruns/closure/NAME')
    args = ap.parse_args()
    output = args.output or HERE/'reruns'/'closure'/args.name
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    state_dir = output/'states'
    if state_dir.exists() and any(state_dir.iterdir()):
        ap.error('Use a fresh output directory; existing state ledgers are not overwritten')
    state_dir.mkdir(exist_ok=True)
    binary = HERE/'noncircular'
    if not binary.exists():
        ap.error('Compile noncircular.cpp as described in README.md')

    def key(payload):
        rows, states, _ = C.parse(payload)
        if 74 not in states:
            return None, len(states), 0
        rooted, reachable = C.traverse(rows, states, 74)
        return C.sha(C.encode(rooted)), len(states), reachable

    payload = args.input.read_bytes()
    root, count, reachable = key(payload)
    if root is None:
        ap.error('Input must retain native start74')
    queue = deque([root])
    seen = {root:{'states':count, 'reachable':reachable, 'parent':None, 'fold':None}}
    (state_dir/(root+'.tm')).write_bytes(payload)
    processed = 0
    minimum = count
    skipped_missing_start = 0
    nonspanning_outputs = 0
    layers = Counter()
    began = time.perf_counter()
    found = False
    with tempfile.TemporaryDirectory(prefix='historyfold_') as temporary:
        prefix = Path(temporary)/'trial'
        while queue and processed < args.max_nodes:
            current = queue.popleft()
            source = state_dir/(current+'.tm')
            process = subprocess.run([str(binary), str(source), str(prefix), str(args.radius), str(args.fuel)], capture_output=True, text=True)
            if process.returncode:
                raise RuntimeError(process.stderr)
            lines = process.stdout.splitlines()
            candidates = sorted(Path(temporary).glob('trial.candidate*.tm'), key=lambda p:int(p.stem.split('candidate')[1]))
            if len(lines) != len(candidates):
                raise ValueError('Candidate/log count mismatch')
            for line, path in zip(lines, candidates):
                candidate = path.read_bytes()
                child, n, nr = key(candidate)
                if child is None:
                    skipped_missing_start += 1
                    continue
                nonspanning_outputs += nr != n
                if child in seen:
                    continue
                seen[child] = {'states':n, 'reachable':nr, 'parent':current, 'fold':line}
                (state_dir/(child+'.tm')).write_bytes(candidate)
                (queue.appendleft if args.strategy == 'dfs' else queue.append)(child)
                if n < minimum:
                    minimum = n
                    print(args.name, 'new minimum', n, 'processed', processed, 'seen', len(seen), flush=True)
                if n < 194:
                    found = True
                    break
            for path in Path(temporary).iterdir():
                path.unlink()
            processed += 1
            layers[seen[current]['states']] += 1
            if processed % 100 == 0:
                print(args.name, 'processed', processed, 'seen', len(seen), 'queue', len(queue), 'minimum', minimum, flush=True)
            if found:
                break
    result = {
        'input':str(args.input), 'input_sha256':hashlib.sha256(payload).hexdigest(),
        'name':args.name, 'radius':args.radius, 'fuel':args.fuel,
        'max_nodes':args.max_nodes, 'strategy':args.strategy, 'processed':processed,
        'unique_rooted_graphs':len(seen), 'remaining_queue':len(queue),
        'minimum_states':minimum, 'sub194_found':found, 'exhausted':not queue,
        'processed_by_states':dict(layers), 'skipped_missing_start':skipped_missing_start,
        'nonspanning_output_occurrences':nonspanning_outputs,
        'elapsed_seconds':time.perf_counter()-began, 'graphs':seen,
    }
    (output/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'graphs'}), flush=True)


if __name__ == '__main__':
    main()
