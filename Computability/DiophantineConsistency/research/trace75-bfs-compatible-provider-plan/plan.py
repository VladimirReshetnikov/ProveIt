#!/usr/bin/env python3
"""Plan a trace75 replay while retaining the captured BFS baseline."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLDPLAN = ROOT / 'research/trace75-fresh-provider-plan/observations/plan-attempt01/result.json'
SCAN = ROOT / 'research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json'
BFS = ROOT / 'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json'
INITIAL = ROOT / 'research/direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json'
SOURCE = ROOT / 'research/trace75-root-probe'
BASE = Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib')
PINS = {OLDPLAN: '053d235687f3024ebb10df6d660d0651797b56096e885f9d88fcb2692138217d',
        SCAN: 'e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d',
        BFS: 'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',
        INITIAL: 'a89c775deee5d7f846e85936f2321c1e91d3d5fd51c62b153c2b2dd8e8540f88'}
OVERLAPS = {'CarrierTransport', 'OffsetBound', 'PellFold', 'PellRankReduction',
            'PellScaledSandwich', 'PellScaledUpper', 'PellVariableGrowth', 'TransportOrder'}


def sha(p):
    return sha256(Path(p).read_bytes()).hexdigest()


def need(value, why):
    if not value:
        raise RuntimeError(why)


def closure(root, headers):
    pending = [root]
    visited = set()
    while pending:
        n = pending.pop()
        if n in visited:
            continue
        visited.add(n)
        pending.extend(headers.get(n, []))
    return visited


def main():
    for path, expected in PINS.items():
        need(sha(path) == expected, 'receipt drift: ' + str(path))
    scan = json.loads(SCAN.read_text())
    old = json.loads(OLDPLAN.read_text())
    bfs = json.loads(BFS.read_text())
    initial = json.loads(INITIAL.read_text())
    need(scan['status'] == old['status'] == bfs['status'] == 'PASS', 'input status')
    baseline = dict(initial)
    need(not set(baseline) & set(bfs['built']), 'baseline name collision')
    baseline.update(bfs['built'])
    need(len(baseline) == 1931, 'baseline size')
    bfs_headers = {n: row['imports'] for n, row in bfs['closure']['project'].items()}
    halt_closure = closure('DirectBFSHaltPellSeed', bfs_headers)
    need(OVERLAPS <= halt_closure, 'halt overlap missing')
    trace_headers = scan['headers']
    names = set(scan['roots']['Trace75FixedCongruence']['project'])
    seeds = set(old['seeds']) | OVERLAPS
    need(seeds <= names, 'seed outside trace closure')
    affected = set(seeds)
    while True:
        newer = affected | {n for n in names if set(trace_headers[n]) & affected}
        if newer == affected:
            break
        affected = newer
    inherited = (affected & names) & set(baseline) - seeds
    stages = (affected & names) - set(baseline)
    need(len(stages) == 31 and all(n.startswith('Trace75') for n in stages), 'stage inventory')
    need(inherited == {'DiophantineConsistency.ModelArithmetic',
                       'DiophantineConsistency.ModelExponentialCongruence',
                       'PellOddFold', 'PellRecovery'}, 'inherited nodes changed')
    for n in inherited:
        oldrec = baseline[n]['.olean']
        tracerec = scan['selected_project'][n]['.olean']
        need(oldrec['sha256'] == tracerec['sha256'], 'inherited object differs: ' + n)
    remain = set(stages)
    order = []
    while remain:
        layer = sorted(n for n in remain if not (set(trace_headers[n]) & remain))
        need(layer, 'cycle in selected project graph')
        order.extend(layer)
        remain.difference_update(layer)
    producers = {}
    for n in order:
        src = SOURCE / (n + '.lean')
        objhash = scan['selected_project'][n]['.olean']['sha256']
        matches = []
        for receipt in sorted((SOURCE / 'observations').glob('*/terminal.json')):
            data = json.loads(receipt.read_text())
            if data.get('exit') != 0 or data.get('reason') is not None or data.get('object_sha256') != objhash:
                continue
            snap, out, err = (receipt.parent / x for x in ('source.txt', 'stdout', 'stderr'))
            if not all(p.is_file() for p in (snap, out, err)) or sha(snap) != sha(src):
                continue
            if sha(out) != data['stdout_sha256'] or sha(err) != data['stderr_sha256']:
                continue
            if err.read_text() or re.search(r'(?i)\b(?:warning|error)(?:\([^:\n]*\))?:|\bsorryAx\b', out.read_text()):
                continue
            matches.append((receipt, out, err))
        need(matches, 'no matching clean source/producer: ' + n)
        receipt, out, err = matches[-1]
        imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', src.read_text(), re.M)
        need(imports == [x for x in trace_headers[n] if x != 'Init'], 'source/header mismatch: ' + n)
        producers[n] = {'source': str(src), 'source_sha256': sha(src),
                        'receipt': str(receipt), 'receipt_sha256': sha(receipt),
                        'object_sha256': objhash, 'stage_imports': [m for m in imports if m in stages],
                        'stdout_sha256': sha(out), 'stderr_sha256': sha(err)}
    for n in OVERLAPS:
        need(n in baseline and n in old['classification']['different'], 'overlap classification: ' + n)
        need(baseline[n]['.olean']['sha256'] != scan['selected_project'][n]['.olean']['sha256'],
             'overlap no longer differs: ' + n)
    for path, expected in PINS.items():
        need(sha(path) == expected, 'receipt changed: ' + str(path))
    result = {'status': 'PASS', 'scope': 'static source-pinned replay plan; no Lean build or full '
              'historical/package/dynamic ancestry claim', 'inputs': {str(p): h for p, h in PINS.items()},
              'runner_sha256': sha(__file__), 'root': 'Trace75FixedCongruence',
              'seeds': sorted(seeds), 'preserved_bfs_overlap': sorted(OVERLAPS),
              'affected': sorted(affected), 'inherited_baseline_affected': sorted(inherited),
              'stage_order': order, 'producers': producers, 'classification': old['classification']}
    obs = HERE / 'observations/plan-attempt01'
    need(not os.path.lexists(obs), 'observation exists')
    obs.mkdir(parents=True)
    target = obs / 'result.json'
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'stages': len(order), 'inherited': len(inherited),
                      'sha256': sha(target)}))


if __name__ == '__main__':
    main()
