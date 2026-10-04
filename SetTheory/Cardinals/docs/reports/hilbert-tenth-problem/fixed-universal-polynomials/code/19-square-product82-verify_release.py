#!/usr/bin/env python3
"""Authenticate the final release, excluding only its top-level manifest."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
def main():
    expected = json.loads((ROOT / 'MANIFEST.json').read_text())['sha256']
    actual = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(ROOT.rglob('*')) if p.is_file() and p != ROOT / 'MANIFEST.json'}
    if actual != expected:
        raise RuntimeError(json.dumps({
            'missing': sorted(set(expected)-set(actual)),
            'extra': sorted(set(actual)-set(expected)),
            'changed': sorted(k for k in set(actual)&set(expected) if actual[k] != expected[k])}))
    print(json.dumps({'status': 'PASS', 'files_authenticated': len(actual),
                      'top_level_manifest_excludes_itself': True}, sort_keys=True))
if __name__ == '__main__':
    main()

