#!/usr/bin/env python3
"""Compare peer stages 97–101 without assuming different objects equivalent."""
from collections import Counter
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


for name, root in [('author', AUTHOR), ('peer', PEER)]:
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(RUNNER),
                        '--output', str(root), '--check'], cwd=ROOT,
                       capture_output=True, text=True, timeout=120)
    out = r.stdout.strip(); parts = out.split()
    ok = (out == 'ALL_STAGES_RECORDED 104' or
          (name == 'peer' and len(parts) >= 4 and parts[0] == 'READY_NO_LEAN' and
           parts[1].isdigit() and int(parts[1]) >= 101 and parts[2] == 'completed;'))
    need(r.returncode == 0 and not r.stderr and ok, (name, r.returncode, out, r.stderr))

ma, mb = [json.loads((root / 'manifest.json').read_text()) for root in (AUTHOR, PEER)]
need(ma['modules'] == mb['modules'] and ma['runner_sha256'] == mb['runner_sha256'] == digest(RUNNER),
     'plan or runner mismatch')
rows = []
special = {}
for i in range(97, 102):
    receipts = [root / 'receipts' / f'{i:03d}.json' for root in (AUTHOR, PEER)]
    a, b = [json.loads(p.read_text()) for p in receipts]
    need(a['status'] == b['status'] == 'PASS' and
         a['module'] == b['module'] == ma['modules'][i-1]['module'] and
         a['source_sha256'] == b['source_sha256'], ('source or status mismatch', i))
    la, lb = [Path(r['log']).read_text().replace(r['command'][5], '<SOURCE>') for r in (a, b)]
    need(la == lb, ('normalized compiler log mismatch', i))
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
    if i in (98, 99, 100, 101):
        objects = [Path(r['output']['resolved']).read_bytes() for r in (a, b)]
        paths = [r['command'][5].encode() for r in (a, b)]
        positions = [o.find(p) for o, p in zip(objects, paths)]
        need(positions[0] == positions[1] and positions[0] >= 24 and
             all(o.count(p) == 1 for o, p in zip(objects, paths)), ('path layout', i))
        pos = positions[0]
        spans = [((len(p)+1+7)//8)*8 for p in paths]
        for obj, path, span in zip(objects, paths, spans):
            fields = [int.from_bytes(obj[pos-24+j:pos-16+j], 'little') for j in (0, 8, 16)]
            need(fields == [len(path)+1, len(path)+1, len(path)] and
                 obj[pos+len(path):pos+span] == bytes(span-len(path)), ('path fields', i))
        z = objects[0][:pos-24] + objects[1][pos-24:pos+spans[1]] + objects[0][pos+spans[0]:]
        need(len(z) == len(objects[1]) and len(z) % 8 == 0, ('length after replacement', i))
        diff = [(int.from_bytes(z[k:k+8], 'little') -
                 int.from_bytes(objects[1][k:k+8], 'little')) % (1 << 64)
                for k in range(0, len(z), 8) if z[k:k+8] != objects[1][k:k+8]]
        counts = Counter(diff)
        need(not counts,
             ('unexpected residual object differences', i, counts.most_common(5)))
        special[str(i)] = {'author_length': len(objects[0]), 'peer_length': len(objects[1]),
                           'path_offset': pos, 'author_path_padded_length': spans[0],
                           'peer_path_padded_length': spans[1],
                           'remaining_aligned_word_delta_counts': dict(counts)}

need([r['objects_equal'] for r in rows] == [True, False, False, False, False], 'object outcome changed')
need([len(r['direct_hash_differences']) for r in rows] == [0, 1, 1, 1, 2],
     'direct input mismatch pattern changed')
print(json.dumps({'status': 'STAGES_97_TO_101_COMPILED_OBJECT_DIFFERENCES_REMAIN',
                  'runner_sha256': digest(RUNNER), 'stages': rows, 'object_byte_observations': special,
                  'scope': 'byte observations only; no Lean serialization semantics, exact paired match, '
                           'full ancestry audit, or endpoint replay'}, indent=2, sort_keys=True))
