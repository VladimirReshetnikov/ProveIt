#!/usr/bin/env python3
"""Verify the attributed, bounded source fixture. Integrity is not authentication."""
from pathlib import Path
import hashlib
import json
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify_manifest as manifest
ROOT=Path(__file__).absolute().parent
EXPECTED=frozenset(('data/oeis_prefix.json',))


def verify(root=ROOT):
    root=manifest.check_directory(root)
    receipt=manifest.load_json(manifest.read_regular(root/'data/SOURCE_DATA_HASHES.json'))
    manifest.need(isinstance(receipt,dict),'source receipt must be an object')
    manifest.need(receipt.get('retrieved_utc_date')=='2026-10-03','unexpected source date')
    files=receipt.get('files')
    manifest.need(isinstance(files,dict) and set(files)==EXPECTED,'source data inventory differs')
    for name,info in files.items():
        manifest.safe_name(name)
        manifest.check_directory((root/name).parent)
        content=manifest.read_regular(root/name)
        manifest.need(isinstance(info,dict) and set(info)=={'bytes','sha256'},'invalid source receipt')
        manifest.need(type(info['bytes']) is int and len(content)==info['bytes'],'source data size differs: '+name)
        manifest.need(hashlib.sha256(content).hexdigest()==info['sha256'],'source data digest differs: '+name)
    return {'status':'PASS','source_files_checked':len(files),'retrieved_utc_date':receipt['retrieved_utc_date']}


if __name__=='__main__':
    print(json.dumps(verify(),sort_keys=True))
