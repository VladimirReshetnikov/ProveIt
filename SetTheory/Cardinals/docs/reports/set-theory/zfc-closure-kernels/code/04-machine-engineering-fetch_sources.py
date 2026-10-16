#!/usr/bin/env python3
"""Fetch immutable public upstream audit inputs and verify every byte hash.

No source is executed by this command. --verify-only performs no network
requests and does not create or change files. Existing mismatched files are
never overwritten. Invoke explicitly before the audit commands.
"""
import argparse
import hashlib
import json
from pathlib import Path
import urllib.request


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=here/'sources')
    ap.add_argument('--verify-only', action='store_true')
    a = ap.parse_args()
    manifest = json.loads((here/'sources_manifest.json').read_text())
    if not a.verify_only:
        a.output.mkdir(parents=True, exist_ok=True)
    for spec in manifest['files']:
        name = spec['filename']
        if Path(name).name != name:
            raise ValueError('manifest filenames must be simple basenames')
        target = a.output/name
        if target.exists():
            data = target.read_bytes()
        elif a.verify_only:
            raise FileNotFoundError(target)
        else:
            request = urllib.request.Request(spec['url'], headers={'User-Agent':'ProveIt-TM-research-audit'})
            with urllib.request.urlopen(request, timeout=60) as response:
                data = response.read()
        digest = hashlib.sha256(data).hexdigest()
        if digest != spec['sha256'] or len(data) != spec['bytes']:
            raise ValueError(f'{name}: size/SHA256 mismatch; existing files were not overwritten')
        if not target.exists() and not a.verify_only:
            with target.open('xb') as handle:
                handle.write(data)
        print(f'{name}: {len(data)} bytes; SHA256 {digest}')


if __name__ == '__main__':
    main()
