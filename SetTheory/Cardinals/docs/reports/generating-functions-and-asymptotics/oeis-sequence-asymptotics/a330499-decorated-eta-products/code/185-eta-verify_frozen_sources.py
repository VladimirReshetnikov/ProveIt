#!/usr/bin/env python3
"""Check exact-kernel and factual-provenance bytes against the release receipt.

The receipt is not a signature: coordinated replacement can defeat a hash list.
The complete distributable additionally has SHA256SUMS.json.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify_manifest as manifest
ROOT=Path(__file__).absolute().parent
EXPECTED=frozenset(('code/verify_exact.py','code/test_exact_guards.py',
                    'certificates/exact_checks.json','data/fixture21.json','data/provenance.json'))

def verify(root=ROOT):
    root=manifest.check_directory(root)
    data=manifest.load_json(manifest.read_regular(root/'data/FROZEN_SOURCE_HASHES.json'))
    manifest.need(isinstance(data,dict) and set(data)=={'report','release_date_utc','files'},'invalid freeze receipt schema')
    manifest.need(type(data['report']) is int and data['report']==185 and data['release_date_utc']=='2026-10-03','unexpected freeze identity')
    files=data['files']
    manifest.need(isinstance(files,dict) and set(files)==EXPECTED,'frozen source inventory mismatch')
    for name,wanted in files.items():
        manifest.safe_name(name)
        path=root/name
        manifest.check_directory(path.parent)
        content=manifest.read_regular(path)
        manifest.need(isinstance(wanted,dict) and set(wanted)=={'bytes','sha256'},'invalid frozen file receipt')
        manifest.need(type(wanted['bytes']) is int and wanted['bytes']>=0 and len(content)==wanted['bytes'],'frozen source length differs: '+name)
        manifest.need(isinstance(wanted['sha256'],str) and hashlib.sha256(content).hexdigest()==wanted['sha256'],'frozen source hash differs: '+name)
    return {'status':'PASS','frozen_files_checked':len(files),'release_date_utc':data['release_date_utc']}

if __name__=='__main__':
    try:
        print(json.dumps(verify(),sort_keys=True))
    except (ValueError,OSError,KeyError,TypeError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        sys.exit(1)
