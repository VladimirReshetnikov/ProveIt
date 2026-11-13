#!/usr/bin/env python3
"""Audit stages 31–35 of the bounded nine-variable peer replay."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
RUNNER = DC / 'research/nine-variable-ipra/bounded-build-preflight/replay.py'
AUTHOR = Path('/tmp/nine-ipra-guarded-author-20261102-h')
PEER = Path('/tmp/nine-ipra-guarded-peer-20261102-a')


def need(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def normalize(value, root):
    if isinstance(value, str):
        return value.replace(str(root), '<ROOT>')
    if isinstance(value, list):
        return [normalize(item, root) for item in value]
    if isinstance(value, dict):
        return {normalize(k, root): normalize(v, root) for k, v in value.items()}
    return value


for name, root in [('author', AUTHOR), ('peer', PEER)]:
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                          '--output', str(root), '--check'], cwd=ROOT,
                         capture_output=True, text=True, timeout=120)
    output = run.stdout.strip(); words = output.split()
    ok = (output == 'ALL_STAGES_RECORDED 104' or
          (name == 'peer' and len(words) >= 4 and words[0] == 'READY_NO_LEAN' and
           words[1].isdigit() and int(words[1]) >= 35 and words[2] == 'completed;'))
    need(run.returncode == 0 and not run.stderr and ok, (name, run.returncode, output, run.stderr))

a_manifest, b_manifest = [json.loads((root / 'manifest.json').read_text())
                           for root in (AUTHOR, PEER)]
need(a_manifest['modules'] == b_manifest['modules'] and
     a_manifest['runner_sha256'] == b_manifest['runner_sha256'] == digest(RUNNER),
     'plan or runner mismatch')
rows = []
for index in range(31, 36):
    paths = [root / 'receipts' / f'{index:03d}.json' for root in (AUTHOR, PEER)]
    a, b = [json.loads(path.read_text()) for path in paths]
    need(a['status'] == b['status'] == 'PASS' and
         a['module'] == b['module'] == a_manifest['modules'][index-1]['module'] and
         a['source_sha256'] == b['source_sha256'] and
         a['output']['sha256'] == b['output']['sha256'], ('source/output mismatch', index))
    need(normalize(a['direct'], AUTHOR) == normalize(b['direct'], PEER) and
         normalize(a['direct_guards'], AUTHOR) == normalize(b['direct_guards'], PEER),
         ('direct dependency or companion mismatch', index))
    need(a['warning_policy'] is None and b['warning_policy'] is None,
         ('unexpected warning policy', index))
    logs = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, b)]
    need(logs[0] == logs[1] and not any(x in logs[0] for x in ('warning:', 'error:', 'sorryAx')),
         ('compiler output mismatch', index))
    rows.append({'stage': index, 'module': a['module'], 'source_sha256': a['source_sha256'],
                 'object_sha256': a['output']['sha256'], 'direct_modules': len(a['direct']),
                 'direct_candidate_guards': len(a['direct_guards']),
                 'author_receipt_sha256': digest(paths[0]), 'peer_receipt_sha256': digest(paths[1]),
                 'normalized_log_sha256': sha256(logs[0].encode()).hexdigest()})
print(json.dumps({'status': 'STAGES_31_TO_35_MATCH_SCOPED', 'runner_sha256': digest(RUNNER),
                  'stages': rows, 'scope': 'recorded source, direct inputs and companions, '
                           'outputs and logs only; historical transitive, package and dynamic '
                           'ancestry and endpoints remain outside scope'}, indent=2, sort_keys=True))
