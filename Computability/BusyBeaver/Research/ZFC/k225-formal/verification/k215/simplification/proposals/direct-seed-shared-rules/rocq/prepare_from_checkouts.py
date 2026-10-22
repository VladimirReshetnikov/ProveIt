#!/usr/bin/env python3
"""Restore the exact inputs from pinned checkouts and verify their identities.

Usage: python3 prepare_from_checkouts.py --proveit /path/to/ProveIt
       --jeff-reference /path/to/busy-beaver --k230-reference /path/to/k230-rocq

The three checkouts are read only.  The KCode230 provider uses LF normalization,
recorded in source_manifest.json; every other input is retained byte for byte.
"""
import argparse, hashlib, json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser()
p.add_argument('--proveit',type=Path,required=True)
p.add_argument('--jeff-reference',type=Path,required=True)
p.add_argument('--k230-reference',type=Path,required=True)
a=p.parse_args()
roots={'ProveIt':a.proveit,'busy-beaver':a.jeff_reference,'k230-rocq':a.k230_reference}
manifest=json.loads((ROOT/'evidence/source_manifest.json').read_text())
for x in manifest['inputs']:
    raw=(roots[x['repository']]/x['source_path']).read_bytes()
    if x['normalization']=='CRLF to LF':
        raw=raw.replace(b'\r\n',b'\n')
    if hashlib.sha256(raw).hexdigest()!=x['sha256']:
        raise SystemExit('Pinned input mismatch: '+x['source_path'])
    target=ROOT/x['packet_path']
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(raw)
    print(x['packet_path'])
