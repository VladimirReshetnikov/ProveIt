#!/usr/bin/env python3
"""Extract the exact small compressed fixture input from the pinned package.

The source fixture is inherited data. This script never executes inherited
Python or C++ code. It verifies both compressed and decompressed identities.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

RELATIVE = 'inputs/state_reduction/candidate245-literal-cases.txt.gz'
COMPRESSED_SHA256 = '3ebf4ea86da4a6bcd12b857cb67b3ba6b32e597b94eb8bfeef5e3ff03cddf31d'
RAW_SHA256 = '71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--routing-package', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source = args.routing_package / RELATIVE
    compressed = source.read_bytes()
    if hashlib.sha256(compressed).hexdigest() != COMPRESSED_SHA256:
        raise ValueError('The routing245 compressed fixture identity does not match.')
    raw = gzip.decompress(compressed)
    if hashlib.sha256(raw).hexdigest() != RAW_SHA256:
        raise ValueError('The decompressed fixture identity does not match.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(raw)
    print(json.dumps(dict(status='PASS', output=str(args.output), bytes=len(raw),
        sha256=RAW_SHA256, source=str(source)), indent=2))

if __name__ == '__main__':
    main()
