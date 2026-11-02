#!/usr/bin/env python3
"""Compare pinned declared source inventories; does not validate compiled imports."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
NEW = HERE / 'manifest.json'
OLD = ROOT / 'research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay/source-freeze-evidence-03/manifest.json'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

if sha(NEW) != 'fcc52c38ba2b7ccd54b8125a9ec600ecc63a9641851cd03744146c6de95e0ff4':
    raise ValueError('new manifest mismatch')
if sha(OLD) != '9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded':
    raise ValueError('70-source manifest mismatch')
a = json.loads(NEW.read_text())['sources']
b = json.loads(OLD.read_text())['sources']
common = set(a) & set(b)
drift = sorted(n for n in common if a[n]['sha256'] != b[n]['sha256'])
result = {'new_modules': len(a), 'old_modules': len(b), 'shared': len(common),
          'shared_source_drift': drift, 'new_only': len(set(a)-set(b)),
          'old_only': len(set(b)-set(a))}
if result != {'new_modules': 1140, 'old_modules': 70, 'shared': 64,
              'shared_source_drift': [], 'new_only': 1076, 'old_only': 6}:
    raise ValueError(result)
print(json.dumps(result, sort_keys=True))
