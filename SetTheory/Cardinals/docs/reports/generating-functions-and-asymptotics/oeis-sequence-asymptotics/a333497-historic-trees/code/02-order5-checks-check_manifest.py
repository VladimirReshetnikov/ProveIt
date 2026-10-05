#!/usr/bin/env python3
"""Closed, duplicate-safe file-inventory/SHA-256 checker; Python standard library.

Usage: python check_manifest.py ROOT
       python check_manifest.py ROOT --write
The sole manifest is ROOT/MANIFEST.json. It is excluded from its own inventory.
No security claim is made for a manifest supplied by an untrusted party.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

class ManifestError(Exception): pass

def need(ok,code,detail):
    if not ok: raise ManifestError(f'{code}: {detail}')

def pairs(items):
    out={}
    for k,v in items:
        need(k not in out,'MANIFEST_DUPLICATE_KEY',f'duplicate JSON key {k}')
        out[k]=v
    return out

def inventory(root):
    need(root.is_dir() and not root.is_symlink(),'MANIFEST_ROOT','root must be an ordinary directory')
    result={}
    for item in sorted(root.rglob('*')):
        rel=item.relative_to(root).as_posix()
        need(not item.is_symlink(),'MANIFEST_SYMLINK',f'symlink forbidden: {rel}')
        if item.is_dir(): continue
        need(item.is_file(),'MANIFEST_FILE_TYPE',f'nonregular file forbidden: {rel}')
        if rel=='MANIFEST.json': continue
        blob=item.read_bytes()
        result[rel]={'path':rel,'bytes':len(blob),'sha256':hashlib.sha256(blob).hexdigest()}
    return result

def verify(root):
    manifest=root/'MANIFEST.json'
    need(manifest.is_file() and not manifest.is_symlink(),'MANIFEST_FILE','missing or symlinked MANIFEST.json')
    try: data=json.loads(manifest.read_text(),object_pairs_hook=pairs)
    except (OSError,UnicodeError,json.JSONDecodeError) as exc: raise ManifestError(f'MANIFEST_JSON: {exc}') from exc
    need(type(data) is dict and set(data)=={'schema_version','files'},'MANIFEST_SCHEMA','expected exactly schema_version and files')
    need(type(data['schema_version']) is int and data['schema_version']==1,'MANIFEST_VERSION','expected integer version 1')
    need(type(data['files']) is list and data['files'],'MANIFEST_RECORDS','nonempty files list required')
    indexed={}
    for row in data['files']:
        need(type(row) is dict and set(row)=={'path','bytes','sha256'},'MANIFEST_RECORD_SCHEMA','expected exactly path, bytes, sha256')
        p=row['path']
        need(type(p) is str and bool(p) and '\x00' not in p and '\\' not in p and
             not p.startswith('/') and all(part not in ('','.','..') for part in p.split('/')) and
             PurePosixPath(p).as_posix()==p and p!='MANIFEST.json',
             'MANIFEST_PATH','noncanonical, absolute, self-referential, or traversal path')
        need(p not in indexed,'MANIFEST_DUPLICATE_PATH',f'duplicate path {p}')
        need(type(row['bytes']) is int and row['bytes']>=0,'MANIFEST_BYTES',f'invalid byte count for {p}')
        need(type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}',row['sha256']),
             'MANIFEST_HASH_FORMAT',f'invalid SHA-256 for {p}')
        indexed[p]=row
    actual=inventory(root)
    need(set(actual)==set(indexed),'MANIFEST_INVENTORY',
         f'missing={sorted(set(indexed)-set(actual))}; extra={sorted(set(actual)-set(indexed))}')
    for p,row in indexed.items():
        need(actual[p]['bytes']==row['bytes'],'MANIFEST_SIZE',f'byte count changed: {p}')
        need(actual[p]['sha256']==row['sha256'],'MANIFEST_HASH',f'SHA-256 changed: {p}')
    return len(actual)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root',type=Path)
    ap.add_argument('--write',action='store_true',help='generate/replace manifest before verification')
    args=ap.parse_args()
    try:
        if args.write:
            data={'schema_version':1,'files':list(inventory(args.root).values())}
            (args.root/'MANIFEST.json').write_text(json.dumps(data,indent=2)+'\n')
        count=verify(args.root)
        print(f'MANIFEST_PASS {count} files')
        return 0
    except ManifestError as exc:
        print(f'MANIFEST_FAILED {exc}',file=sys.stderr)
        return 2
if __name__=='__main__':sys.exit(main())
