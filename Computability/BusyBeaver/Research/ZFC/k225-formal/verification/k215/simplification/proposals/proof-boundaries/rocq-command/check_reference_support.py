#!/usr/bin/env python3
"""Verify the two arithmetic dependencies against the pinned external source.

This reads bytes only. It neither compiles nor modifies either checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',required=True,type=Path)
    p.add_argument('--reference',required=True,type=Path)
    args=p.parse_args()
    evidence=json.loads((HERE/'evidence/reference-support-provenance.json').read_text())
    manifest=json.loads((args.reference/'manifest.json').read_bytes())
    for item in evidence['sources']:
        raw=(args.reference/item['reference_path']).read_bytes()
        retained=(args.repo/item['retained_repository_path']).read_bytes()
        digest=hashlib.sha256(raw).hexdigest()
        assert digest==item['reference_sha256']==manifest['local_files'][item['reference_path']]
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        assert blob==item['reference_tree_blob_sha1']
        assert hashlib.sha256(retained).hexdigest()==item['retained_sha256']
        assert raw.replace(b'\r\n',b'\n')==retained
        print(item['module']+': identical after CRLF -> LF only')
    print('PASS: definitions and proofs match the pinned external support files exactly')

if __name__=='__main__': main()
