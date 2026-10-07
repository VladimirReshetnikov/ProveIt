#!/usr/bin/env python3
"""Verify a release ZIP against its separate receipt, without extracting it."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import stat
import zipfile

def need(ok,message):
    if not ok: raise RuntimeError(message)

def sha(b):return hashlib.sha256(b).hexdigest()

p=argparse.ArgumentParser()
p.add_argument('zip',type=Path)
p.add_argument('receipt',type=Path)
a=p.parse_args()
obj=json.loads(a.receipt.read_text())
need(obj['schema']==1,'Receipt schema')
need(a.zip.is_file() and not a.zip.is_symlink(),'ZIP must be a regular file')
need(sha(a.zip.read_bytes())==obj['zip_sha256'],'Whole-ZIP identity mismatch')
with zipfile.ZipFile(a.zip) as z:
    infos=z.infolist();names=[x.filename for x in infos]
    need(len(names)==len(set(names)),'Duplicate ZIP members')
    need(set(names)==set(obj['members']),'Actual ZIP member inventory mismatch')
    for info in infos:
        name=info.filename;path=PurePosixPath(name)
        need(not path.is_absolute() and '\\' not in name and str(path)==name and
             all(x not in ('','.','..') for x in path.parts),'Unsafe ZIP member')
        need(not info.is_dir() and not stat.S_ISLNK(info.external_attr >> 16),'Non-file ZIP member')
        need(sha(z.read(info))==obj['members'][name],'ZIP member bytes mismatch '+name)
print(json.dumps({'status':'PASS','whole_zip_sha256':obj['zip_sha256'],
                  'actual_members_checked':len(obj['members']),'assertions_required':False},
                 indent=2,sort_keys=True))
