#!/usr/bin/env python3
"""Compare the first five bounded replay stages against the author ledger.

This is an incremental comparison, not a full dependency-ancestry audit.
"""
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


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def normalize(value, root):
    if isinstance(value, str):
        return value.replace(str(root), '<ROOT>')
    if isinstance(value, list):
        return [normalize(x, root) for x in value]
    if isinstance(value, dict):
        return {normalize(k, root): normalize(v, root) for k, v in value.items()}
    return value


for name, root in [('author', AUTHOR), ('peer', PEER)]:
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                        '--output', str(root), '--check'], cwd=ROOT,
                       capture_output=True, text=True, timeout=120)
    output = r.stdout.strip()
    if name == 'author':
        acceptable = output == 'ALL_STAGES_RECORDED 104'
    else:
        words = output.split()
        acceptable = (output == 'ALL_STAGES_RECORDED 104' or
                      (len(words) >= 4 and words[0] == 'READY_NO_LEAN' and
                       words[1].isdigit() and int(words[1]) >= 5 and words[2] == 'completed;'))
    need(r.returncode == 0 and not r.stderr and acceptable, (name, r.returncode, r.stdout, r.stderr))

author_manifest = json.loads((AUTHOR / 'manifest.json').read_text())
peer_manifest = json.loads((PEER / 'manifest.json').read_text())
need(author_manifest['modules'] == peer_manifest['modules'], 'different stage plans')
need(author_manifest['runner_sha256'] == peer_manifest['runner_sha256'] == digest(RUNNER),
     'runner hash mismatch')

# Inspect the exact bounded stage-2 object difference.  Each object contains
# one source pathname, preceded by three 64-bit little-endian length fields.
# This is a byte comparison, not a theorem about Lean's serialization format.
stage2 = [json.loads((root / 'receipts/002.json').read_text()) for root in (AUTHOR, PEER)]
objects = [Path(r['output']['resolved']).read_bytes() for r in stage2]
paths = [r['command'][5].encode() for r in stage2]
positions = [obj.find(path) for obj, path in zip(objects, paths)]
need(len(objects[0]) == len(objects[1]) and positions[0] == positions[1] and
     positions[0] >= 24 and all(obj.count(path) == 1 for obj, path in zip(objects, paths)),
     'unexpected stage-2 source path layout')
pos = positions[0]
for obj, path in zip(objects, paths):
    fields = [int.from_bytes(obj[pos - 24 + j:pos - 16 + j], 'little') for j in (0, 8, 16)]
    need(fields == [len(path) + 1, len(path) + 1, len(path)], ('unexpected path fields', fields))
span = ((max(map(len, paths)) + 1 + 7) // 8) * 8
for obj, path in zip(objects, paths):
    need(obj[pos + len(path):pos + span] == bytes(span - len(path)), 'nonzero path padding')
normalized = bytearray(objects[0])
normalized[pos-24:pos+span] = objects[1][pos-24:pos+span]
need(bytes(normalized) == objects[1], 'other stage-2 binary differences')
author_stage2_hash = stage2[0]['output']['sha256']
peer_stage2_hash = stage2[1]['output']['sha256']
need(author_stage2_hash == sha256(objects[0]).hexdigest() and
     peer_stage2_hash == sha256(objects[1]).hexdigest() and
     author_stage2_hash != peer_stage2_hash, 'stage-2 hash mismatch or equality')


def align_stage2_hash(value):
    if isinstance(value, str):
        return value.replace(peer_stage2_hash, author_stage2_hash)
    if isinstance(value, list):
        return [align_stage2_hash(x) for x in value]
    if isinstance(value, dict):
        return {k: align_stage2_hash(v) for k, v in value.items()}
    return value


rows = []
for i in range(1, 6):
    receipts = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, PEER)]
    a, b = [json.loads(p.read_text()) for p in receipts]
    need(a['status'] == b['status'] == 'PASS', ('bad status', i))
    need(a['module'] == b['module'] == author_manifest['modules'][i-1]['module'],
         ('module mismatch', i))
    need(a['source_sha256'] == b['source_sha256'], ('source mismatch', i))
    need(i == 2 or a['output']['sha256'] == b['output']['sha256'], ('object mismatch', i))
    need(normalize(a['direct'], AUTHOR) == align_stage2_hash(normalize(b['direct'], PEER)),
         ('direct mismatch', i))
    need(normalize(a['direct_guards'], AUTHOR) == align_stage2_hash(normalize(b['direct_guards'], PEER)),
         ('direct guard mismatch', i))
    sa = Path(a['command'][5]); sb = Path(b['command'][5])
    la = Path(a['log']).read_text().replace(str(sa), '<SOURCE>')
    lb = Path(b['log']).read_text().replace(str(sb), '<SOURCE>')
    need(la == lb, ('compiler output mismatch', i))
    rows.append({'stage': i, 'module': a['module'], 'source_sha256': a['source_sha256'],
                 'author_object_sha256': a['output']['sha256'],
                 'peer_object_sha256': b['output']['sha256'],
                 'normalized_log_sha256': sha256(la.encode()).hexdigest(),
                 'warning_count': la.count('warning:'),
                 'direct_module_count': len(a['direct']),
                 'direct_guard_count': len(a['direct_guards']),
                 'author_receipt_sha256': digest(receipts[0]),
                 'peer_receipt_sha256': digest(receipts[1])})
print(json.dumps({'status': 'FIRST_FIVE_COMPARED_STAGE2_PATH_BYTES_DIFFER',
                  'stage2_source_path_offset': pos,
                  'stage2_normalized_region': [pos-24, pos+span],
                  'stage2_normalization': 'replace three path length fields and padded source path bytes; '
                                          'all other bytes are equal',
                  'runner_sha256': digest(RUNNER),
                  'author_manifest_sha256': digest(AUTHOR / 'manifest.json'),
                  'peer_manifest_sha256': digest(PEER / 'manifest.json'),
                  'stages': rows,
                  'scope': 'five incremental stages; inherited historical transitive, '
                           'package and dynamic ancestry; no endpoint replay'},
                 indent=2, sort_keys=True))
