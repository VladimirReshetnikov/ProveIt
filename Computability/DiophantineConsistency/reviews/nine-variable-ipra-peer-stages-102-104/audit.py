#!/usr/bin/env python3
"""Compare peer stages 102–104 without assuming different objects equivalent."""
from collections import Counter
from hashlib import sha256
import json
import re
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


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


for name, root in [('author', AUTHOR), ('peer', PEER)]:
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                        '--output', str(root), '--check'], cwd=ROOT,
                       capture_output=True, text=True, timeout=120)
    out = r.stdout.strip(); parts = out.split()
    ok = (out == 'ALL_STAGES_RECORDED 104' or
          (name == 'peer' and len(parts) >= 4 and parts[0] == 'READY_NO_LEAN' and
           parts[1].isdigit() and int(parts[1]) >= 104 and parts[2] == 'completed;'))
    need(r.returncode == 0 and not r.stderr and ok, (name, r.returncode, out, r.stderr))

ma, mb = [json.loads((root / 'manifest.json').read_text()) for root in (AUTHOR, PEER)]
need(ma['modules'] == mb['modules'] and ma['runner_sha256'] == mb['runner_sha256'] == digest(RUNNER),
     'plan or runner mismatch')
rows = []
for i in range(102, 105):
    receipts = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, PEER)]
    a, b = [json.loads(p.read_text()) for p in receipts]
    need(a['status'] == b['status'] == 'PASS' and
         a['module'] == b['module'] == ma['modules'][i-1]['module'] and
         a['source_sha256'] == b['source_sha256'], ('source or status mismatch', i))
    la, lb = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, b)]
    need(la == lb, ('normalized compiler log mismatch', i))
    if i == 104:
        reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", la, re.S)
        names = re.findall(r'^#print axioms (\S+)', Path(a['command'][5]).read_text(), re.M)
        need(len(reports) == len(names) == 4 and
             [x[0].rsplit('.', 1)[-1] for x in reports] == names and
             all({z.strip() for z in axioms.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
                 for _, axioms in reports), 'unexpected endpoint axiom reports')
    direct = [{name: entry['record']['sha256'] for name, entry in r['direct'].items()} for r in (a, b)]
    changed = [{'module': name, 'author_sha256': direct[0].get(name),
                'peer_sha256': direct[1].get(name)}
               for name in sorted(direct[0].keys() | direct[1].keys())
               if direct[0].get(name) != direct[1].get(name)]
    rows.append({'stage': i, 'module': a['module'], 'source_sha256': a['source_sha256'],
                 'author_object_sha256': a['output']['sha256'],
                 'peer_object_sha256': b['output']['sha256'],
                 'objects_equal': a['output']['sha256'] == b['output']['sha256'],
                 'normalized_log_sha256': sha256(la.encode()).hexdigest(),
                 'warning_count': la.count('warning:'), 'direct_hash_differences': changed,
                 'author_receipt_sha256': digest(receipts[0]), 'peer_receipt_sha256': digest(receipts[1])})

need([r['objects_equal'] for r in rows] == [True, True, True], 'object outcome changed')
need([len(r['direct_hash_differences']) for r in rows] == [1, 2, 1],
     'direct input mismatch pattern changed')
print(json.dumps({'status': 'STAGES_102_TO_104_OUTPUTS_MATCH_IMPORTS_DIFFER',
                  'runner_sha256': digest(RUNNER), 'stages': rows,
                  'scope': 'byte observations only; no Lean serialization semantics, exact paired match, '
                           'full ancestry audit, or endpoint replay'}, indent=2, sort_keys=True))
