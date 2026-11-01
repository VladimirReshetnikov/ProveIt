#!/usr/bin/env python3
"""Compare available rebuilt artifacts to hashes from the historical 848-module state.

These are hashes of direct imports only; agreement does not establish equality
of transitive dependencies or compatibility of all inherited project objects.
"""
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
STATE = Path('/tmp/pra14-full-transitive-2x6o__to/state.json')
STATE_SHA = '67a9223288a4c5ffb582d70db63d27ad224fd2474c49ce12811f745d673daa91'
MANIFEST = HERE / 'input-manifest.json'
MANIFEST_SHA = '491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if len(sys.argv) != 3:
        raise SystemExit('usage: compare_historical.py /absolute/build/root /new/output.json')
    root = Path(sys.argv[1]).resolve(strict=True)
    output = Path(sys.argv[2])
    if sha(STATE) != STATE_SHA or sha(MANIFEST) != MANIFEST_SHA:
        raise RuntimeError('historical state or input manifest identity changed')
    state = json.loads(STATE.read_text())
    hashes = defaultdict(set)
    for record in state['records']:
        for name, value in record.get('dependency_hashes', {}).items():
            if name.startswith('Foundation.'):
                hashes[name].add(value)
    if len(state['records']) != 848 or any(len(values) != 1 for values in hashes.values()):
        raise RuntimeError('historical record count or direct hash uniqueness changed')
    lib = root / '.lake/build/lib/lean'
    rows = []
    for name, values in sorted(hashes.items()):
        obj = lib.joinpath(*name.split('.')).with_suffix('.olean')
        new_hash = sha(obj) if obj.is_file() else None
        old_hash = next(iter(values))
        rows.append({'module': name, 'historical_sha256': old_hash,
                     'fresh_sha256': new_hash,
                     'matches': None if new_hash is None else new_hash == old_hash})
    result = {'historical_state_sha256': STATE_SHA, 'input_manifest_sha256': MANIFEST_SHA,
              'driver_sha256': sha(Path(__file__)), 'root': str(root), 'rows': rows,
              'available': sum(r['matches'] is not None for r in rows),
              'matched': sum(r['matches'] is True for r in rows),
              'mismatched': sum(r['matches'] is False for r in rows),
              'scope': 'Point-in-time direct object hashes only; no transitive or replay compatibility claim.'}
    if sha(STATE) != STATE_SHA or sha(MANIFEST) != MANIFEST_SHA:
        raise RuntimeError('inputs changed during comparison')
    with output.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write('\n')
    print('available:', result['available'], 'matched:', result['matched'],
          'mismatched:', result['mismatched'])

if __name__ == '__main__':
    main()
