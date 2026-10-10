#!/usr/bin/env python3
"""Guarded LOCAL integration; dry-run by default. Never contacts GitHub.

Usage:
  python integration/apply_integration.py --repo /path/to/ProveIt
  python integration/apply_integration.py --repo /path/to/ProveIt --apply

Requires exact inspected blobs. Review the default unified-diff output first.
The source package and proof certificates should be retained with the report.
"""
from __future__ import annotations
from argparse import ArgumentParser
from pathlib import Path
import difflib
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent

def blob_sha(data:bytes)->str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def confined(base:Path, relative:str)->Path:
    result=(base/relative).resolve()
    if not result.is_relative_to(base.resolve()):
        raise ValueError(f'Path escapes destination: {relative}')
    return result

def prepare(repo:Path,manifest:dict):
    base=confined(repo,manifest['base_directory'])
    changes=[]
    for edit in manifest['edits']:
        dest=confined(base,edit['path'])
        data=dest.read_bytes()
        if blob_sha(data)!=edit['expected_blob']:
            raise ValueError(f'Snapshot mismatch: {dest}. No files were written. Review and merge manually.')
        old=data.decode('utf-8');new=old
        for replacement in edit['replacements']:
            needle=replacement['old']
            if new.count(needle)!=1:
                raise ValueError(f'Expected one exact replacement anchor in {dest}')
            new=new.replace(needle,replacement['new'],1)
        changes.append((dest,data,new.encode('utf-8')))
    for addition in manifest['new_files']:
        dest=confined(base,addition['destination'])
        if dest.exists():raise ValueError(f'Refusing to overwrite new-file destination: {dest}')
        source=confined(HERE,addition['source'])
        changes.append((dest,None,source.read_bytes()))
    return changes

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--apply',action='store_true',help='Write the already validated local changes')
    args=p.parse_args();repo=args.repo.resolve()
    manifest=json.loads((HERE/'edits.json').read_text())
    changes=prepare(repo,manifest)  # All validation happens before the first write.
    for dest,old,new in changes:
        relative=str(dest.relative_to(repo))
        if old is None:
            print(f'ADD {relative} ({len(new)} bytes)')
        else:
            print(''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),
                           fromfile='a/'+relative,tofile='b/'+relative)),end='')
    if not args.apply:
        print('\nDRY RUN: no files were written. Review the changes before using --apply.')
        return
    written=[]
    try:
        for dest,old,new in changes:
            dest.parent.mkdir(parents=True,exist_ok=True)
            written.append((dest,old));dest.write_bytes(new)
    except Exception:
        for dest,old in reversed(written):
            if old is None:dest.unlink(missing_ok=True)
            else:dest.write_bytes(old)
        raise
    print('\nApplied local changes. Review git diff and run the manuscript build. No remote changes were made.')

if __name__=='__main__':
    try:main()
    except (OSError,ValueError) as exc:
        print(f'ERROR: {exc}',file=sys.stderr);raise SystemExit(1)
