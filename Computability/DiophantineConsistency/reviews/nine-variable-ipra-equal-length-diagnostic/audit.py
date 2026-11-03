#!/usr/bin/env python3
"""Audit author versus equal-length-source-root stage 1–6 diagnostic."""
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
VERIFY = Path('/tmp/nine-ipra-guarded-verify-20261102-a')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


need(len(str(AUTHOR)) == len(str(VERIFY)), 'source root lengths differ')
for name, root in [('author', AUTHOR), ('verify', VERIFY)]:
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                        '--output', str(root), '--check'], cwd=ROOT,
                       capture_output=True, text=True, timeout=120)
    words = r.stdout.strip().split()
    acceptable = (r.stdout.strip() == 'ALL_STAGES_RECORDED 104' or
                  (name == 'verify' and len(words) >= 4 and words[0] == 'READY_NO_LEAN' and
                   words[1].isdigit() and int(words[1]) >= 6 and words[2] == 'completed;'))
    need(r.returncode == 0 and not r.stderr and acceptable,
         (name, r.returncode, r.stdout, r.stderr))

ma, mb = [json.loads((root / 'manifest.json').read_text()) for root in (AUTHOR, VERIFY)]
need(ma['modules'] == mb['modules'] and ma['runner_sha256'] == mb['runner_sha256'] == digest(RUNNER),
     'plan or runner mismatch')
rows = []
for i in range(1, 7):
    receipts = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, VERIFY)]
    a, b = [json.loads(p.read_text()) for p in receipts]
    need(a['status'] == b['status'] == 'PASS' and
         a['module'] == b['module'] == ma['modules'][i-1]['module'] and
         a['source_sha256'] == b['source_sha256'], ('source or status mismatch', i))
    la, lb = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, b)]
    need(la == lb, ('normalized compiler log mismatch', i))
    direct = [{name: entry['record']['sha256'] for name, entry in r['direct'].items()} for r in (a, b)]
    changed = [{'module': name, 'author_sha256': direct[0].get(name),
                'verify_sha256': direct[1].get(name)}
               for name in sorted(direct[0].keys() | direct[1].keys())
               if direct[0].get(name) != direct[1].get(name)]
    objects = [Path(r['output']['resolved']).read_bytes() for r in (a, b)]
    paths = [r['command'][5].encode() for r in (a, b)]
    need(len(paths[0]) == len(paths[1]) and len(objects[0]) == len(objects[1]), ('size mismatch', i))
    if i in (2, 6):
        need(objects[0].count(paths[0]) == objects[1].count(paths[1]) == 1 and
             objects[0].replace(paths[0], paths[1]) == objects[1], ('non-path difference', i))
        need(objects[0] != objects[1], ('unexpected equal object', i))
    else:
        need(objects[0] == objects[1], ('unexpected object difference', i))
    rows.append({'stage': i, 'module': a['module'], 'source_sha256': a['source_sha256'],
                 'author_object_sha256': a['output']['sha256'],
                 'verify_object_sha256': b['output']['sha256'],
                 'objects_equal': objects[0] == objects[1],
                 'equal_after_path_replacement': objects[0].replace(paths[0], paths[1]) == objects[1],
                 'source_path_occurrences': [objects[0].count(paths[0]), objects[1].count(paths[1])],
                 'normalized_log_sha256': sha256(la.encode()).hexdigest(),
                 'direct_hash_differences': changed,
                 'author_receipt_sha256': digest(receipts[0]), 'verify_receipt_sha256': digest(receipts[1])})
need([len(r['direct_hash_differences']) for r in rows] == [0, 0, 0, 1, 0, 0],
     'direct hash difference pattern changed')
need(rows[3]['direct_hash_differences'][0]['module'] == 'DiophantineConsistency.ModelDifferenceRing',
     'unexpected stage-4 import difference')
print(json.dumps({'status': 'EQUAL_LENGTH_DIAGNOSTIC_STAGES_1_TO_6_COMPARED',
                  'author_root_length': len(str(AUTHOR)), 'verify_root_length': len(str(VERIFY)),
                  'runner_sha256': digest(RUNNER), 'stages': rows,
                  'scope': 'complete object byte comparison with source-path replacement only; '
                           'no semantics of Lean object serialization, full ancestry, or endpoint replay'},
                 indent=2, sort_keys=True))
