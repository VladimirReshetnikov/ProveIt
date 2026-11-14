#!/usr/bin/env python3
"""Offline replay of six fixed-family cyclic merger searches.

With no options, verify the recorded inputs/results and replay only the short
bootstraps and rejected diagnostic. Use --smoke to compile the three C++17
engines and check a small positive fixture. Use --all to rerun the six searches.
No internet, Git checkout, or proof assistant is required.
"""
from pathlib import Path
import argparse
import json
import os
import re
import shlex
import subprocess
import tempfile
import time
from audit_support import BASE, read_json, read_table, read_contexts, sha256, write_json
from augment_bootstrap import augment

DONE = re.compile(r'^DONE pairs=(\d+) partial=(\d+) full=(\d+)$', re.MULTILINE)


def completed(log):
    matches = DONE.findall(Path(log).read_text())
    assert len(matches) == 1, log
    pair, partial, full = map(int, matches[0])
    assert Path(log).read_text().splitlines()[-1].startswith('DONE ')
    return {'pairs': pair, 'partial_zero_rows': partial, 'hits': full}


def diagnostic(manifest):
    item = manifest['diagnostic']
    baseline, _, _ = read_table(BASE / manifest['context_cases']['even']['native_table'])
    expected = {(q, b): (w, d, 88 if n == 301 else n)
                for (q, b), (w, d, n) in baseline.items() if q != 301}
    expected[88, 0] = (0, -1, 51)
    expected[51, 0] = (0, 1, 122)
    rows, states, halt = read_table(BASE / item['table'])
    assert rows == expected and len(states) == 194
    frozen = read_json(BASE / item['receipt'])
    q, h, ones, trace = 74, 0, set(), []
    for _ in range(frozen['steps']):
        b = int(h in ones)
        w, d, n = rows[q, b]
        trace.append([q, h, b, w, d, n])
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        q, h = n, h + d
    assert trace == frozen['trace']
    assert (q, h, sorted(ones)) == (frozen['q'], frozen['h'], frozen['ones'])
    assert h not in ones
    w, d, n = rows[q, 0]
    assert n == q
    assert not ones or (d == 1 and h > max(ones)) or (d == -1 and h < min(ones))
    return {'status': 'CERTIFIED_OUTWARD_RAY', 'working_states': 194,
            'steps': frozen['steps'], 'state': q, 'head': h,
            'ones': sorted(ones), 'zero_transition': [w, d, n],
            'trace_comparison': 'Exact full transition trace, not digest-only.',
            'interpretation': 'Rejected blank initialization of this fixed even/runtime composition; not a lower bound.'}


def verify_recorded(manifest):
    for relative, digest in manifest['file_sha256'].items():
        assert sha256(BASE / relative) == digest, relative
    searches = {}
    for item in manifest['searches']:
        rows, states, halt = read_table(BASE / item['table'])
        assert len(states) == item['working_states']
        expected_pairs = (len(states) - 1) * (len(states) - 2) // 2
        assert expected_pairs == item['expected']['pairs']
        assert completed(BASE / item['log']) == item['expected']
        assert (BASE / item['hits']).read_bytes() == b''
        assert item['expected']['hits'] == 0
        if item['contexts']:
            pairs = read_contexts(BASE / item['contexts'], item['radius'])
            assert {q for q, _ in pairs} <= states
        searches[item['name']] = item['expected']
    contexts = {}
    for name, item in manifest['context_cases'].items():
        pairs, receipt = augment(BASE / item['native_table'], BASE / item['source_contexts'],
                                 item['bootstrap_steps'], 6, 74)
        assert pairs == read_contexts(BASE / item['augmented_contexts'], 6), name
        assert receipt['endpoint']['state'] == 84 and receipt['endpoint']['head'] == -2
        collector = read_json(BASE / item['collector_receipt'])
        assert collector['validation']['ok'] and collector['radius'] == 6
        assert collector['contexts'] == receipt['source_contexts']
        frozen = read_json(BASE / item['bootstrap_receipt'])
        receipt['augmented_contexts_sha256'] = sha256(BASE / item['augmented_contexts'])
        assert receipt == frozen, name
        contexts[name] = {key: receipt[key] for key in
                          ('transitions', 'source_contexts', 'augmented_contexts',
                           'added_contexts', 'includes_final_endpoint')}
    assert sum(v['pairs'] for v in searches.values()) == 111747
    return {'status': 'PASS', 'mode': 'recorded integrity and finite replay',
            'verified_file_hashes': len(manifest['file_sha256']),
            'recorded_searches': searches, 'pair_instances': 111747,
            'accepted_mergers': 0, 'bootstrap_replays': contexts,
            'diagnostic': diagnostic(manifest),
            'limits': 'The six full searches and symbolic context collectors were not rerun in this mode. Finite bootstraps and the ray trace were freshly replayed.'}


def compile_engines(manifest, build, cxx):
    commands = {}
    for source in sorted({item['source'] for item in manifest['searches']}):
        executable = build / Path(source).stem
        command = shlex.split(cxx) + ['-std=c++17', '-O3', str(BASE / source), '-o', str(executable)]
        subprocess.run(command, check=True, capture_output=True, text=True)
        commands[source] = executable
    return commands


def smoke(manifest, executables, output):
    expected_fold = {'remove': 1, 'keep': 2, 'actions': [[0, -1, 3], [1, 1, 3]]}
    results = {}
    for source, executable in executables.items():
        name = Path(source).stem
        cmd = [str(executable), str(BASE / 'smoke/fixture.tm'), '1', '8']
        if name == 'cyclic_source':
            cmd.append(str(BASE / 'smoke/contexts.tsv'))
        run = subprocess.run(cmd, check=True, capture_output=True, text=True)
        hits = [json.loads(line) for line in run.stdout.splitlines() if line.strip()]
        assert expected_fold in hits, source
        log = output / (name + '_smoke.log')
        log.write_text(run.stderr)
        (output / (name + '_smoke_hits.jsonl')).write_text(run.stdout)
        parsed = completed(log)
        assert parsed['pairs'] == 3 and parsed['hits'] == len(hits)
        results[name] = dict(parsed, known_duplicate_fold_found=True)
    return {'status': 'PASS', 'mode': 'compile and positive four-state smoke fixture',
            'radius': 1, 'fuel': 8, 'engines': results,
            'limits': 'Checks compilation and a known accepted merge. Does not repeat or replace the six recorded searches.'}


def rerun(manifest, executables, selected, output):
    results = {}
    for item in manifest['searches']:
        if selected and item['name'] not in selected:
            continue
        name = item['name']
        command = [str(executables[item['source']]), str(BASE / item['table']),
                   str(item['radius']), str(item['fuel'])]
        if item['contexts']:
            command.append(str(BASE / item['contexts']))
        print(f'Rerunning {name}: radius {item["radius"]}, fuel {item["fuel"]} ...', flush=True)
        log = output / (name + '.log')
        hits = output / (name + '_hits.jsonl')
        started = time.monotonic()
        with hits.open('w') as stdout, log.open('w') as stderr:
            subprocess.run(command, stdout=stdout, stderr=stderr, check=True)
        parsed = completed(log)
        assert parsed == item['expected'], (name, parsed, item['expected'])
        assert hits.read_bytes() == (BASE / item['hits']).read_bytes()
        results[name] = dict(parsed, elapsed_seconds=round(time.monotonic() - started, 3))
        print(f'{name}: PASS; {parsed["pairs"]} pairs, zero hits.', flush=True)
    return {'status': 'PASS', 'mode': 'fresh complete selected searches', 'searches': results,
            'scope': manifest['scope']}


def main():
    if not __debug__:
        raise SystemExit('Do not use Python -O: assertions are verification checks.')
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group()
    group.add_argument('--verify-only', action='store_true', help='Default: integrity and short exact replays.')
    group.add_argument('--smoke', action='store_true', help='Also compile C++17 and run a small positive fixture.')
    group.add_argument('--all', action='store_true', help='Compile and rerun all six recorded searches.')
    group.add_argument('--case', action='append', choices=('even_cyclic', 'even_blank', 'even_source',
                                                          'primary_source', 'ax11q6_blank', 'ax11q6_source'),
                       help='Compile and rerun one named search; option may be repeated.')
    ap.add_argument('--out', type=Path, default=BASE / 'replay-output')
    ap.add_argument('--cxx', default=os.environ.get('CXX', 'g++'), help='C++17 compiler command; default g++.')
    args = ap.parse_args()
    manifest = read_json(BASE / 'search_manifest.json')
    args.out.mkdir(parents=True, exist_ok=True)
    verification = verify_recorded(manifest)
    write_json(args.out / 'integrity_receipt.json', verification)
    print('Recorded integrity, exact bootstrap unions, and diagnostic ray: PASS.', flush=True)
    if args.smoke or args.all or args.case:
        with tempfile.TemporaryDirectory(prefix='compiler-', dir=args.out) as temporary:
            executables = compile_engines(manifest, Path(temporary), args.cxx)
            if args.smoke:
                result = smoke(manifest, executables, args.out)
                write_json(args.out / 'smoke_receipt.json', result)
            else:
                result = rerun(manifest, executables, args.case, args.out)
                write_json(args.out / 'fresh_search_receipt.json', result)
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps(verification, indent=2))


if __name__ == '__main__':
    main()
