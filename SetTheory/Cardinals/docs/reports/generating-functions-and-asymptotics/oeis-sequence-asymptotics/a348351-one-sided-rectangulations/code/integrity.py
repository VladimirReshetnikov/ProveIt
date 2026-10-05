#!/usr/bin/env python3
"""Strict distributable inventory and SHA-256 verifier; not a proof checker."""
from hashlib import sha256
from pathlib import Path, PurePosixPath
import argparse
import json
import re

ROOT=Path(__file__).resolve().parent
MANIFEST='manifest.json'
IGNORED_DIRS={'build','qa','__pycache__'}
IGNORED_FILES={MANIFEST,'report111_source_checks.zip','FINAL_SHA256.txt'}

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def inventory():
    result={}
    for p in ROOT.rglob('*'):
        relative=p.relative_to(ROOT)
        if relative.parts[0] in {'build','qa'} or '__pycache__' in relative.parts:
            continue
        if len(relative.parts)==1 and p.name in IGNORED_FILES:
            continue
        require(not p.is_symlink(),f'symlink forbidden: {relative}')
        if p.is_file():
            content=p.read_bytes()
            result[relative.as_posix()]={'sha256':sha256(content).hexdigest(),'size_bytes':len(content)}
    return result

def unique_object(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,f'duplicate JSON key: {key}')
        result[key]=value
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--generate',action='store_true',help='explicitly replace manifest from present distributable files')
    args=ap.parse_args()
    actual=inventory()
    if args.generate:
        required={'report111.tex','report111.pdf','build.py','README.md','replay.py',
                  'integrity_corruption_test.py','integrity.py','seal.py','validation/sources.json',
                  'checks/verify_report111.py','checks/mutation_campaign.py',
                  'checks/report111_fixture.json'}
        require(required<=set(actual),'cannot seal incomplete package')
        (ROOT/MANIFEST).write_text(json.dumps({'schema':1,'files':actual},indent=2,sort_keys=True)+'\n')
        print(f'WROTE: {len(actual)} file manifest')
        return
    manifest=json.loads((ROOT/MANIFEST).read_text(),object_pairs_hook=unique_object)
    require(set(manifest)=={'schema','files'} and type(manifest['schema']) is int and manifest['schema']==1,'invalid manifest schema')
    expected=manifest['files']
    require(isinstance(expected,dict),'invalid manifest files')
    for path,record in expected.items():
        p=PurePosixPath(path)
        require(not p.is_absolute() and '..' not in p.parts and '\\' not in path and str(p)==path,
                f'unsafe manifest path: {path}')
        require(isinstance(record,dict) and set(record)=={'sha256','size_bytes'},f'invalid record: {path}')
        require(type(record['size_bytes']) is int and record['size_bytes']>=0,f'invalid size: {path}')
        require(isinstance(record['sha256'],str) and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None,
                f'invalid hash: {path}')
    require(set(actual)==set(expected),f'inventory mismatch: {sorted(set(actual)^set(expected))}')
    for path in expected:
        require(actual[path]==expected[path],f'integrity mismatch: {path}')
    print(f'PASS: strict inventory and SHA-256 of {len(expected)} files')

if __name__=='__main__':
    main()
