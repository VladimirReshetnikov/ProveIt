#!/usr/bin/env python3
"""Six clean equality substitutions on two pinned K219 allocators.

This measures raw allocation and decoder-prefix binding, not primitive runtime.
The speculative CI6-right entry is tried only after its exact missing-entry
error and is reported separately. No delivered main or proof compiler runs.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
COMPILERS = HERE.parent / 'k219-continuation-search/compiler-inputs'
BASE = HERE.parent / 'candidate-k219'
HITS = REPO / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-res-enc-eq_clean_hits.json'
PINS = {
    'measure.py': '342537f773807e185ed250a18db27afe5122abf2b8bda0e8a31f073e0d1ca397',
    'measure_protected.py': 'e487791755559f994024ecb1ccebd232f8686e329fe8220ae720af4d98c24413',
    'measure_ci6_hypothesis.py': '2585938f7e976392fc0f030d07d79743436cdec6d009307ba512391d39963719',
    'measure_protected_ci6_hypothesis.py': 'c227dca7e90767fe8c0f722e011459670ae9e10317e89deb0bdee726c542ed30',
    'source_language.py': '4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
    'build221.py': '3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
}
SOURCE_PINS = {
    0: '7d1eb32fdeac6a0169f5b2209b7c2303e2c6120f958f5b08ba6316b742fa1052',
    1: '4c0d6065d80e2f19e4babaa8e9367e40fb97cfd28df48c613ebe4a0621ccafa9',
    2: 'f5c9a64cd571cb764bb00fff84f519df75f4381df3ec0ce51eced6d29ec28b64',
    3: '36a80a7ecdff6ed91f4fdb369bc2ba70d0e2c08c443e511d83a77c9218770eee',
    12: 'fdf75965da5268238c1d1a7cb5f940a394a034074c5b3c3479e4d0234f291ee5',
}
PATHS = ['111010010011101111000', '11101001001110111110', '1110100101100', '111110']

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
    need(not args.output.exists(), 'Output must be fresh')
    inputs = {str(COMPILERS / name): value for name, value in PINS.items()}
    inputs.update({
        str(BASE / 'sites219.json'): '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',
        str(BASE / 'k219.native.tm'): 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26',
        str(HITS): '6b9a424830dd28216c6b20524900d01faac832d4b80bc9147eb03c0ce86f7c6b',
    })
    inputs.update({str(HERE / f'candidates/hit{i:02d}.sites.json'): value for i, value in SOURCE_PINS.items()})
    need(all(sha(Path(p)) == h for p, h in inputs.items()), 'Pinned input drift')
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(COMPILERS))
    s = importlib.import_module('source_language')
    b = importlib.import_module('build221')
    old_rows = json.loads((BASE / 'sites219.json').read_text())
    old = s.tree(old_rows)
    table = b.read_table((BASE / 'k219.native.tm').read_bytes())
    hits = list(map(freeze, json.loads(HITS.read_text())))
    need(s.metrics(old)['dag_nodes'] == 206 and len(table) == 438, 'Baseline census')
    need(s.graph_arithmetic(old_rows)[0] == s.graph_intervals(old_rows), 'Baseline CFG')
    args.output.mkdir(parents=True)
    (args.output / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    started = time.monotonic()
    controls, modules, records = {}, {}, []

    def checked_module(name):
        if name not in modules:
            mod = importlib.import_module(name)
            identity, metrics = mod.compile_tree(s, b, table, old, old)
            need(identity == table and metrics['working_states'] == 219, ('Identity control', name))
            modules[name] = mod
            controls[name] = {'exact_original_table': True, 'metrics': metrics}
        return modules[name]

    def attempt(name, node, output, hypothesis):
        mod = checked_module(name)
        begin = time.monotonic()
        row = {'compiler': name, 'ci6_right_hypothesis': hypothesis}
        missing_ci6 = False
        try:
            compiled, metrics = mod.compile_tree(s, b, table, old, node)
            raw = b.table_bytes(compiled)
            need(b.read_table(raw) == compiled, 'Raw table roundtrip')
            file = output / (name + '.native.tm')
            file.write_bytes(raw)
            row.update(status='DECODER_PREFIX_BINDING_PASS', metrics=metrics,
                       raw_file=str(file.relative_to(args.output)), raw_sha256=sha(file),
                       helper302_retained=any(q == 302 for q, bit in compiled))
        except (ValueError, KeyError, AssertionError) as exc:
            row.update(status='COMPILER_REJECTED', error=repr(exc))
            detail = exc.args[0] if len(exc.args) == 1 else None
            missing_ci6 = (isinstance(exc, ValueError) and isinstance(detail, tuple)
                           and detail[:3] == ('No generic leaf entry', ('CI', 6), 1))
        row['seconds'] = time.monotonic() - begin
        dump(output / (name + '.json'), row)
        return row, missing_ci6

    for index in (0, 1, 2, 3, 12, 11):
        paths = []
        def subst(node, path=''):
            if node == hits[10]:
                paths.append(path)
                return hits[index]
            return node if s.leaf(node) else (subst(node[0], path+'0'), subst(node[1], path+'1'))
        node = subst(old)
        need(paths == PATHS, ('Exact four equality occurrences', index, paths))
        rows = s.sites(node)
        need(s.graph_arithmetic(rows)[0] == s.graph_intervals(rows), ('Candidate CFG', index))
        expected_leaves = 4744 if index in (2, 11) else 4748
        need(len(rows) == expected_leaves, ('Candidate leaf count', index))
        need(s.metrics(node)['dag_nodes'] == (206 if index == 11 else 207), ('Candidate DAG', index))
        if index in SOURCE_PINS:
            need(rows == json.loads((HERE / f'candidates/hit{index:02d}.sites.json').read_text()), 'Existing exact source')
        output = args.output / f'hit{index:02d}'
        output.mkdir()
        (output / 'sites.json').write_bytes(s.compact(rows))
        record = {'hit': index, 'source_file': f'hit{index:02d}/sites.json',
                  'source_sha256': sha(output / 'sites.json'), 'metrics': s.metrics(node),
                  'replaced_paths': paths, 'independent_cfg_agreement': True, 'allocations': []}
        for name, alternative in [('measure', 'measure_ci6_hypothesis'),
                                  ('measure_protected', 'measure_protected_ci6_hypothesis')]:
            outcome, missing_ci6 = attempt(name, node, output, False)
            record['allocations'].append(outcome)
            if missing_ci6:
                outcome2, _ = attempt(alternative, node, output, True)
                outcome2['trigger'] = outcome['error']
                record['allocations'].append(outcome2)
        records.append(record)
        dump(output / 'result.json', record)
        print('HIT', index, [(r['compiler'], r['status'], r.get('metrics', {}).get('working_states')) for r in record['allocations']], flush=True)
    need(all(sha(Path(p)) == h for p, h in inputs.items()), 'Input changed during measurement')
    passing = [(r['hit'], a) for r in records for a in r['allocations'] if a['status'] == 'DECODER_PREFIX_BINDING_PASS']
    result = {'status': 'SIX_EQUALITY_ALLOCATION_MEASUREMENTS_COMPLETE', 'inputs': inputs,
              'compiler_identity_controls': controls, 'records': records,
              'minimum_raw_states': min(a['metrics']['working_states'] for i, a in passing) if passing else None,
              'at_most218': [{'hit': i, **a} for i, a in passing if a['metrics']['working_states'] <= 218],
              'scope': 'All-natural equality substitutions preserve the source contract by separate ordinary proofs. Allocations check only the exact decoder prefix. No primitive runtime/startup, Lean/Rocq, or calibrated binary candidate claim. CI6-right 1R13 remains an explicit unverified hypothesis.',
              'seconds': time.monotonic()-started, 'reviewed_script_sha256': sha(Path(__file__))}
    dump(args.output / 'result.json', result)
    print(json.dumps({k: v for k, v in result.items() if k not in ('inputs', 'compiler_identity_controls', 'records')}, indent=2), flush=True)

if __name__ == '__main__':
    main()
