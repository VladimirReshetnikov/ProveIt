#!/usr/bin/env python3
"""Verify Report58's full inventory or make a deterministic external ZIP.
The seal command creates MANIFEST.json once, after review. No scientific code runs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = 'MANIFEST.json'
STAMP = (2026, 10, 4, 0, 0, 0)

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def encode(value):
    return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()

def read_regular(p):
    st = p.lstat()
    need(stat.S_ISREG(st.st_mode), 'Not a regular file: '+str(p))
    need(st.st_nlink == 1, 'Hard-linked files are not accepted: '+str(p))
    with p.open('rb') as f:
        raw=f.read()
    need(len(raw)==st.st_size, 'File changed while reading: '+str(p))
    return raw

def inventory():
    entries={}
    def walk(directory):
        for p in sorted(directory.iterdir()):
            name=str(p.relative_to(ROOT))
            if name==MANIFEST:
                need(stat.S_ISREG(p.lstat().st_mode), 'Manifest must be a regular file')
                continue
            st=p.lstat()
            need(not stat.S_ISLNK(st.st_mode), 'Symlink rejected: '+name)
            need(not any(c in ('__pycache__','.git','.DS_Store') or c.startswith('.') for c in p.relative_to(ROOT).parts), 'Unexpected hidden/cache entry: '+name)
            if stat.S_ISDIR(st.st_mode):
                entries[name]={'kind':'directory'}
                walk(p)
            else:
                raw=read_regular(p)
                entries[name]={'kind':'file','bytes':len(raw),'sha256':digest(raw)}
    walk(ROOT)
    return entries

def verify():
    raw=read_regular(ROOT/MANIFEST)
    data=json.loads(raw)
    need(data.get('schema')=='report58-release-v1','Unsupported manifest schema')
    need(data.get('entries')==inventory(),'Release inventory or file-byte mismatch')
    need(encode(data)==raw,'Manifest is not canonical JSON')
    return data,raw

def safe_new_output(raw):
    need(raw.startswith('/') and not raw.startswith('//'),'Output must be canonical absolute path')
    p=Path(raw)
    need(str(p)==raw and all(x not in ('.','..') for x in raw.split('/')),'Noncanonical output path')
    for q in reversed([p,*p.parents]):
        if os.path.lexists(q):
            st=q.lstat()
            need(not stat.S_ISLNK(st.st_mode),'Symlink path rejected: '+str(q))
            need(q==p or stat.S_ISDIR(st.st_mode),'Output ancestor is not a directory')
        else:
            need(q==p,'Output parent does not exist')
    need(not os.path.lexists(p),'Output already exists')
    need(p!=ROOT and ROOT not in p.parents and p not in ROOT.parents,'Output must be external to release')
    return p

def main():
    need(sys.flags.isolated==1 and sys.flags.no_site==1 and sys.dont_write_bytecode and sys.flags.optimize==0,
         'Invoke with python3 -I -S -B and no optimization')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('seal','verify','zip'))
    ap.add_argument('--output')
    args=ap.parse_args()
    if args.action=='seal':
        need(args.output is None,'Seal does not take output')
        need(not os.path.lexists(ROOT/MANIFEST),'Manifest already exists; do not overwrite a seal')
        data={'schema':'report58-release-v1','report':'Report58','date_utc':'2026-10-04',
          'scope':'Complete release inventory, excluding this self-referential manifest; no scientific program is executed by this tool.',
          'archive':{'format':'ZIP_STORED','timestamp':list(STAMP),'file_mode':'0644','directory_entries':True},
          'entries':inventory()}
        for required in ('Report58.tex','Report58.pdf','README.md','verification/REPLAY_RECEIPT.json','verification/RENDER_REVIEW.json'):
            need(data['entries'].get(required,{}).get('kind')=='file','Missing regular-file release prerequisite: '+required)
        with (ROOT/MANIFEST).open('xb') as f:f.write(encode(data))
        data,raw=verify()
        print(json.dumps({'status':'PASS','manifest_sha256':digest(raw),'entries':len(data['entries'])},sort_keys=True))
    elif args.action=='verify':
        need(args.output is None,'Verify does not take output')
        data,raw=verify()
        print(json.dumps({'status':'PASS','manifest_sha256':digest(raw),'entries':len(data['entries'])},sort_keys=True))
    else:
        need(args.output is not None,'ZIP requires --output')
        out=safe_new_output(args.output)
        data,manifest_bytes=verify()
        names=sorted([name+('/' if row['kind']=='directory' else '') for name,row in data['entries'].items()]+[MANIFEST])
        with out.open('xb') as target:
            with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_STORED,allowZip64=True) as z:
                for name in names:
                    raw=b'' if name.endswith('/') else (manifest_bytes if name==MANIFEST else read_regular(ROOT/name))
                    if name!=MANIFEST and not name.endswith('/'):need(digest(raw)==data['entries'][name]['sha256'],'Input changed during archive build')
                    info=zipfile.ZipInfo(name,STAMP);info.create_system=3
                    info.external_attr=((0o40755<<16)|0x10) if name.endswith('/') else (0o100644<<16)
                    info.compress_type=zipfile.ZIP_STORED;info.flag_bits=0
                    z.writestr(info,raw)
        verify()
        with zipfile.ZipFile(out) as z:
            need(z.namelist()==names,'Archive inventory mismatch')
            need(z.testzip() is None,'Archive CRC failure')
            for name in names:
                expected=b'' if name.endswith('/') else (manifest_bytes if name==MANIFEST else read_regular(ROOT/name))
                need(z.read(name)==expected,'Archive byte mismatch')
        print(json.dumps({'status':'PASS','archive':str(out),'bytes':out.stat().st_size,'sha256':digest(out.read_bytes()),'files':len(names)},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:
        print('RELEASE REFUSED: '+str(e),file=sys.stderr)
        raise SystemExit(2)
