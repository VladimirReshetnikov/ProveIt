#!/usr/bin/env python3
"""Reproduce the three source envelopes and exact bootstrap augmentations."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
from audit_support import BASE, read_json, read_contexts, write_contexts, write_json, sha256
from augment_bootstrap import augment


def main():
    if not __debug__:
        raise SystemExit('Do not use Python -O: assertions are verification checks.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case', choices=('all', 'even', 'primary', 'ax11q6'), default='all')
    ap.add_argument('--bootstrap-only', action='store_true',
                    help='Use the recorded source envelopes; freshly replay only the finite bootstraps.')
    ap.add_argument('--out', type=Path, default=BASE / 'context-replay')
    args = ap.parse_args()
    manifest = read_json(BASE / 'search_manifest.json')
    args.out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PA_RESEARCH_REFERENCE_ROOT=str(BASE), PYTHONDONTWRITEBYTECODE='1')
    receipts = {}
    for name, item in manifest['context_cases'].items():
        if args.case != 'all' and args.case != name:
            continue
        for field in ('native_table', 'source_sites', 'source_instructions',
                      'collector', 'source_contexts', 'augmented_contexts'):
            relative = item[field]
            assert sha256(BASE / relative) == manifest['file_sha256'][relative], relative
        recorded_source = BASE / item['source_contexts']
        source = recorded_source
        if not args.bootstrap_only:
            source = args.out / f'{name}_source_k6.tsv'
            print(f'Collecting all symbolic source contexts for {name} ...', flush=True)
            proc = subprocess.run([
                sys.executable, str(BASE / item['collector']),
                str(BASE / item['native_table']), str(BASE / item['source_sites']),
                str(BASE / item['source_instructions']), str(source), '6'],
                env=env, text=True, capture_output=True, check=True)
            fresh = json.loads(proc.stdout)
            frozen = read_json(BASE / item['collector_receipt'])
            assert fresh == frozen, name
            assert source.read_bytes() == recorded_source.read_bytes(), name
            write_json(args.out / f'{name}_context_receipt.json', fresh)
        pairs, receipt = augment(BASE / item['native_table'], source,
                                 item['bootstrap_steps'], 6, 74)
        assert receipt['endpoint']['state'] == 84
        assert receipt['endpoint']['head'] == -2
        assert pairs == read_contexts(BASE / item['augmented_contexts'], 6), name
        output = args.out / f'{name}_source_boot_k6.tsv'
        write_contexts(output, pairs)
        assert output.read_bytes() == (BASE / item['augmented_contexts']).read_bytes(), name
        receipt['augmented_contexts_sha256'] = sha256(output)
        write_json(args.out / f'{name}_bootstrap_receipt.json', receipt)
        receipts[name] = receipt
        print(f'{name}: PASS; {len(pairs)} exact augmented contexts.', flush=True)
    write_json(args.out / 'context_replay_summary.json', {
        'status': 'PASS', 'source_collectors_replayed': not args.bootstrap_only,
        'cases': receipts})


if __name__ == '__main__':
    main()
