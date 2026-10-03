#!/usr/bin/env python3
"""Scan all bundle file bytes for absolute internal location prefixes."""
import argparse
import json
from pathlib import Path

# Split literals keep this scanner from containing the very prefixes it checks.
PATTERNS = {
    'workspace': b'/' + b'workspace',
    'root': b'/' + b'root',
    'home-agent': b'/' + b'home' + b'/' + b'agent',
    'opt-codex': b'/' + b'opt' + b'/' + b'codex',
}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    bundle, output = args.bundle.resolve(), args.output.resolve()
    if not bundle.is_dir():
        parser.error('--bundle must name an existing directory')
    if output.is_relative_to(bundle):
        parser.error('--output must be external to the scanned bundle')
    files = sorted(path for path in bundle.rglob('*') if path.is_file())
    hits = []
    for path in files:
        data = path.read_bytes()
        for label, pattern in PATTERNS.items():
            offset = data.find(pattern)
            if offset >= 0:
                hits.append({'file': path.relative_to(bundle).as_posix(),
                             'pattern_label': label, 'first_byte_offset': offset})
    receipt = {'format': 'absolute-internal-prefix-byte-scan-v1',
               'pattern_labels': sorted(PATTERNS),
               'files_checked': [path.relative_to(bundle).as_posix() for path in files],
               'hits': hits, 'passed': not hits}
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'files_checked': len(files), 'hits': len(hits), 'passed': not hits}, sort_keys=True))
    if hits:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
