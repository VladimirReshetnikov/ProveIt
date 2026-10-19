#!/usr/bin/env python3
"""Replay independent audits using the separately supplied immutable 245 archive.

No network, no upstream mutation, and no extraction into the delivered package.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, shutil, subprocess, sys, zipfile

ARCHIVE_SHA256 = '5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1'
PREFIX = 'zfc245-proof-20261018'

def main():
    if not __debug__:
        raise SystemExit('Assertions must be enabled; do not use python -O.')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True, help='New scratch directory; must not exist')
    p.add_argument('--only', choices=['all', 'literal', 'source', 'runtime', 'encoding'], default='all')
    p.add_argument('--core', action='store_true', help='Also rerun original archive verifier with whole-frame proof')
    a = p.parse_args()
    archive, out = a.archive.resolve(), a.output.resolve()
    if hashlib.sha256(archive.read_bytes()).hexdigest() != ARCHIVE_SHA256:
        raise SystemExit('Original archive SHA-256 mismatch; no files extracted.')
    if out.exists():
        raise SystemExit('Output must not exist; choose a fresh scratch directory.')
    root = Path(__file__).resolve().parent
    shutil.copytree(root / 'research_sub246', out / 'research_sub246')
    research = out / 'research_sub246'
    extraction = research / 'audit245' / 'extracted'
    extraction.mkdir(parents=True)
    with zipfile.ZipFile(archive) as z:
        for entry in z.infolist():
            dest = (extraction / entry.filename).resolve()
            if not dest.is_relative_to(extraction) or not entry.filename.startswith(PREFIX + '/'):
                raise SystemExit('Unsafe or unexpected original archive path.')
            if (entry.external_attr >> 16) & 0o170000 == 0o120000:
                raise SystemExit('Symbolic-link entry is not supported.')
        z.extractall(extraction)
    original = extraction / PREFIX
    runtime_data = research / 'verification' / 'audit245_runtime_copy'
    runtime_data.mkdir()
    for name in ['machine', 'certificate']:
        shutil.copytree(original / name, runtime_data / name)
    selected = ['literal', 'source', 'runtime', 'encoding'] if a.only == 'all' else [a.only]
    jobs = [([sys.executable, '-B', str(research / 'verification' / ('audit245_' + name + ('' if name in ('literal', 'encoding') else '_independent') + '.py'))], out, name) for name in selected]
    if a.core:
        jobs.append(([sys.executable, '-B', 'code/verify_all.py', '--whole-frame'], original, 'original-core-whole-frame'))
    logs = out / 'logs'; logs.mkdir()
    results = []
    for cmd, cwd, name in jobs:
        with (logs / (name + '.log')).open('w') as log:
            run = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
        results.append({'name': name, 'command': cmd, 'returncode': run.returncode, 'log': str(logs / (name + '.log'))})
        print(name, 'PASS' if run.returncode == 0 else 'FAIL', flush=True)
    result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'archive_sha256': ARCHIVE_SHA256, 'checks': results, 'all_pass': all(x['returncode'] == 0 for x in results)}
    (out / 'audit-results.json').write_text(json.dumps(result, indent=2) + '\n')
    return 0 if result['all_pass'] else 1

if __name__ == '__main__':
    sys.exit(main())
