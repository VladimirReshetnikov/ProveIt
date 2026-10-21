#!/usr/bin/env python3
"""Release integrity and independent finite audits; not a kernel replay."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def run(args, cwd=ROOT):
    p = subprocess.run([sys.executable, '-B', *map(str, args)],
                       cwd=cwd, text=True, capture_output=True)
    require(p.returncode == 0, p.stdout + p.stderr)
    return p.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--hashes-only', action='store_true')
    a = ap.parse_args()
    rows = (ROOT / 'SHA256SUMS').read_text().splitlines()
    for line in rows:
        expected, name = line.split('  ', 1)
        path = ROOT / name
        require(path.is_file() and sha(path) == expected, 'Hash mismatch: ' + name)
    print('Release hashes: PASS (%d files)' % len(rows), flush=True)
    if a.hashes_only:
        return

    pin = read(ROOT / 'provenance/repository.json')
    incoming = read(ROOT / 'provenance/incoming.json')
    require(incoming['commit'] == pin['commit'], 'Repository pin mismatch')
    require([x['packet'] for x in incoming['archives']] ==
            ['I' + str(i) for i in range(1, 8)], 'Incoming inventory mismatch')

    normalized = ROOT / 'normalized_rocq'
    run([normalized / 'verify_binding.py'])
    ns = read(normalized / 'verification/compilation-summary.json')
    require(ns['compilation_complete'] and ns['fresh_source_modules'] == 12 and
            ns['additional_interface_modules'] == 2 and
            ns['recursive_source_audit']['exit_code'] == 0,
            'Source proof receipt is not a successful complete focused build')
    print('Normalized source binding and recorded check: PASS', flush=True)

    decoder = ROOT / 'decoder_lean'
    dr = read(decoder / 'verification/receipt.json')
    require(dr['status'] == 'PASS' and dr['fresh_objects'], 'Decoder receipt failure')
    for module in dr['modules']:
        require(module['returncode'] == 0 and
                sha(decoder / module['source']) == module['source_sha256'],
                'Decoder source binding mismatch')
        log = decoder / 'verification/logs' / (module['source'] + '.log')
        require(sha(log) == module['log_sha256'] and 'sorryAx' not in log.read_text(),
                'Decoder log binding mismatch')

    credit = ROOT / 'zero_credit'
    cr = read(credit / 'evidence/receipt.json')
    require(sha(credit / 'TagLowering.v') == cr['source_sha256'] and
            all(x['exit_code'] == 0 for x in cr['results']) and
            cr['closed_assumption_reports'] == 5, 'Zero-credit receipt mismatch')

    with tempfile.TemporaryDirectory(prefix='k215-finite-audit-') as tmp:
        work = Path(tmp)
        run([decoder / 'audit/audit_decoder.py', decoder,
             '--out', work / 'decoder.json'])
        require(read(work / 'decoder.json') == read(decoder / 'audit/evidence.json'),
                'Independent decoder audit differs')
        print('Decoder binding, local replay and malformed controls: PASS', flush=True)
        run([credit / 'compare_markers.py', credit / 'inputs/m124.native.tm',
             credit / 'inputs/fm215.native.tm', '--out', work / 'markers.json'])
        require(read(work / 'markers.json') == read(credit / 'marker-comparison.json'),
                'Marker comparison differs')
        print('Zero-credit recorded check and exact marker comparison: PASS', flush=True)
        run([ROOT / 'search214/verify.py', '--work', work / 'search'])
        sr = read(work / 'search/result.json')
        require(sr['status'] == 'PASS' and not sr['search_replayed'] and
                sr['total_complete_assignments'] == 457682472,
                'Search invariant/control audit mismatch')
        print('All 18 search domains, saved counts and independent controls: PASS', flush=True)

    print('PASS: integrity and finite evidence only; no new kernel or exhaustive-search replay.')


if __name__ == '__main__':
    main()
