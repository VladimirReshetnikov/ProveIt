#!/usr/bin/env python3
"""Check retained CURRENT2011 endpoint observations against live artifacts."""
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
PACKET = DC / 'reviews/nine-variable-ipra-stages-75-81-author-observation'
COPY = PACKET / 'author'
LIVE = Path('/tmp/nine-ipra-guarded-author-20261102-h')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file(), f'non-file or dangling guard: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}


def guard(records):
    for path, expected in records.items():
        need(record(path) == expected, f'guard drift: {path}')


manifest = json.loads((COPY / 'manifest.json').read_text())
results = []
for index in range(75, 82):
    number = f'{index:03d}'
    retained = COPY / 'receipts' / f'{number}.json'
    live = LIVE / 'receipts' / f'{number}.json'
    need(digest(retained) == digest(live), f'receipt drift: {number}')
    item = json.loads(retained.read_text())
    spec = manifest['modules'][index - 1]
    module = spec['module']
    need(item['status'] == 'PASS' and item['module'] == module and
         item['source_sha256'] == spec['source_sha256'], f'receipt mismatch: {number}')
    rel = Path(*module.split('.'))
    source = rel.with_suffix('.lean')
    target = (LIVE / 'lib' / rel).with_suffix('.olean')
    need(digest(COPY / 'src' / source) == spec['source_sha256'] ==
         digest(LIVE / 'src' / source), f'source drift: {module}')
    need(record(target) == item['output'], f'object drift: {module}')
    guard(item['direct_guards'])
    guard(item['warning_policy_guards'])
    attempt = Path(item['log']).parent.relative_to(LIVE)
    for name in ('compile.log', 'deps.stdout', 'deps.stderr'):
        need(digest(COPY / attempt / name) == digest(LIVE / attempt / name),
             f'evidence drift: {attempt / name}')
    log = (COPY / attempt / 'compile.log').read_text()
    need(digest(COPY / attempt / 'compile.log') == item['log_sha256'] and
         not any(word in log for word in ('error:', 'sorryAx')), f'bad log: {module}')
    policy = item['warning_policy']
    if policy is None:
        need('warning:' not in log, f'unexpected warning: {module}')
    else:
        baseline = COPY / 'warning-policies' / f'{number}.log'
        need(digest(baseline) == digest(LIVE / 'warning-policies' / f'{number}.log') and
             log.replace(str(LIVE / 'src' / source), '<SOURCE>') == baseline.read_text(),
             f'warning baseline mismatch: {module}')
    results.append({'stage': index, 'module': module,
                    'direct_guards': len(item['direct_guards'])})

checks = (COPY / 'src/DiophantineConsistency/IPRANineChecks.lean').read_text()
expected = set(re.findall(r'^#print axioms\s+(\S+)', checks, re.M))
last = json.loads((COPY / 'receipts/081.json').read_text())
log = (COPY / Path(last['log']).parent.relative_to(LIVE) / 'compile.log').read_text()
reports = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.M | re.S)
need(len(expected) == len(reports) == 15 and {n for n, _ in reports} == expected,
     'unexpected named reports')
need(all({a.strip() for a in ax.split(',')} == ALLOWED for _, ax in reports),
     'unexpected axiom set')
print(json.dumps({'status': 'PASS_CURRENT_ENDPOINT_AUTHOR_ARTIFACT_AUDIT',
                  'stages': results, 'axiom_reports': len(reports),
                  'scope': 'Point-in-time author audit; no paired replay or full closure.'},
                 sort_keys=True))
