#!/usr/bin/env python3
"""Strict SHA-256 manifest for a report package (not an authenticity signature)."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

MANIFEST='CHECKSUMS.sha256'
class Failure(Exception):
    def __init__(self,name,detail): self.name,self.detail=name,detail

def need(test,name,detail):
    if not test: raise Failure(name,detail)

def included_files(root):
    result={}
    for path in sorted(root.rglob('*')):
        relative=path.relative_to(root)
        need(not path.is_symlink(),'MANIFEST_SYMLINK',relative.as_posix())
        need(path.is_dir() or path.is_file(),'MANIFEST_SPECIAL_FILE',relative.as_posix())
        if path.is_file() and relative.as_posix()!=MANIFEST:
            name=relative.as_posix()
            need('\n' not in name and '\r' not in name and '\\' not in name,'MANIFEST_PATH',name)
            result[name]=hashlib.sha256(path.read_bytes()).hexdigest()
    return result

def run(root,write=False):
    need(root.is_dir(),'MANIFEST_ROOT',str(root))
    actual=included_files(root)
    path=root/MANIFEST
    if write:
        need(bool(actual),'MANIFEST_EMPTY','cannot seal an empty directory')
        path.write_text(''.join(f'{digest}  {name}\n' for name,digest in actual.items()),encoding='utf-8')
    need(path.is_file() and not path.is_symlink(),'MANIFEST_MISSING',MANIFEST)
    expected={}
    for row,line in enumerate(path.read_text(encoding='utf-8').splitlines(),1):
        match=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
        need(match is not None,'MANIFEST_FORMAT',f'row {row}')
        digest,name=match.groups()
        need(not name.startswith('/') and '..' not in Path(name).parts and Path(name).as_posix()==name
             and '\\' not in name and name!=MANIFEST,'MANIFEST_PATH',name)
        need(name not in expected,'MANIFEST_DUPLICATE',name)
        expected[name]=digest
    need(bool(expected),'MANIFEST_EMPTY','no entries')
    for name,digest in expected.items():
        need(name in actual,'MANIFEST_FILE_MISSING',name)
        need(digest==actual[name],'MANIFEST_HASH',name)
    need(set(actual)==set(expected),'MANIFEST_UNLISTED',', '.join(sorted(set(actual)-set(expected))))
    return {'status':'PASS','manifest':MANIFEST,'files':len(actual),'written':write,
            'excluded':[MANIFEST],'note':'Integrity check, not an authenticity signature.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root',type=Path);ap.add_argument('--write',action='store_true');args=ap.parse_args()
    try: obj=run(args.root.resolve(),args.write)
    except Failure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail},indent=2));return 1
    except Exception as e:
        print(json.dumps({'status':'ERROR','diagnostic':'MANIFEST_EXCEPTION','detail':f'{type(e).__name__}: {e}'},indent=2));return 2
    print(json.dumps(obj,indent=2));return 0
if __name__=='__main__':sys.exit(main())
