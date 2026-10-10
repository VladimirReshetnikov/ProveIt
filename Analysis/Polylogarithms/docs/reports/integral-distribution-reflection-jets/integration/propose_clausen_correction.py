#!/usr/bin/env python3
"""Print a proposed source correction; modify a local file ONLY with --apply."""
from __future__ import annotations
import argparse
import difflib
import hashlib
from pathlib import Path
import re

RELATIVE=Path('Analysis/Polylogarithms/docs/manuscript/chapters/02-cyclotomic.tex')
EXPECTED_BLOB='89d2885681b701de3348d6074749fd9288b54b3c'
PATTERN=re.compile(r'Odd Clausen values use\s+the odd character sector\.')
REPLACEMENT=(
    'Imaginary, sine-type cyclotomic values use the odd character sector;\n'
    'real, cosine-type values use the even sector. Under the Clausen\n'
    'convention used here, even-index Clausen functions belong to the odd\n'
    'sector and odd-index Clausen functions belong to the even sector.'
)

def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('repository_or_file',type=Path)
    p.add_argument('--apply',action='store_true',help='write the replacement and preserve a backup')
    p.add_argument('--allow-modified',action='store_true',help='allow applying to a blob other than the inspected version')
    args=p.parse_args()
    path=args.repository_or_file
    if path.is_dir():path=path/RELATIVE
    if not path.is_file():p.error(f'source file not found: {path}')
    data=path.read_bytes();old=data.decode('utf-8')
    if len(PATTERN.findall(old))!=1:
        p.error('expected exactly one old sentence; source is changed or already corrected')
    blob=git_blob_sha(data)
    if args.apply and blob!=EXPECTED_BLOB and not args.allow_modified:
        p.error(f'unexpected blob {blob}; review the dry-run diff before using --allow-modified')
    new=PATTERN.sub(REPLACEMENT,old,count=1)
    print(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),
                                     fromfile=str(path),tofile=str(path)+' (proposed)')),end='')
    if args.apply:
        backup=path.with_name(path.name+'.before-clausen-parity.bak')
        if backup.exists():p.error(f'backup already exists: {backup}')
        backup.write_bytes(data)
        path.write_text(new,encoding='utf-8')
        print(f'Applied; backup: {backup}')
    else:
        print(f'Dry run only. Source Git blob: {blob}')

if __name__=='__main__':main()
