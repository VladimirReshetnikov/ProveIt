#!/usr/bin/env python3
"""Verify the sealed packet inventory and make a deterministic ZIP without overwriting."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, zipfile
R=Path(__file__).resolve().parents[1]
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(name):
    need(isinstance(name,str) and name and '\\' not in name and ':' not in name and '\0' not in name,'Unsafe member')
    p=PurePosixPath(name)
    need(not p.is_absolute() and all(x not in ('','.','..') for x in name.split('/')),'Unsafe member')
    return p
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
need(out!=R and R not in out.parents,'ZIP must be outside packet');need(not out.exists(),'Do not overwrite an existing archive')
manifest=json.loads((R/'manifest.json').read_text());need(manifest['schema_version']==1,'Manifest version');seen=set()
for e in manifest['files']:
    name=e['path'];need(name not in seen and name not in ('manifest.json','SHA256SUMS'),'Duplicate/self manifest member');seen.add(name);f=R/safe(name)
    need(f.is_file() and not f.is_symlink() and R in f.resolve().parents,'Missing/escaping member')
    need(f.stat().st_size==e['size'] and sha(f)==e['sha256'],'Manifest mismatch: '+name)
files=[]
for f in sorted(R.rglob('*')):
    need(not f.is_symlink(),'Symlink in packet')
    if f.is_file():files.append(f)
need({f.relative_to(R).as_posix()for f in files}==seen|{'manifest.json','SHA256SUMS'},'Unexpected inventory')
expected=''.join(f'{sha(f)}  {f.relative_to(R).as_posix()}\n' for f in files if f.name!='SHA256SUMS')
need((R/'SHA256SUMS').read_text()==expected,'SHA256SUMS inventory differs')
out.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
    for f in files:
        i=zipfile.ZipInfo((Path(R.name)/f.relative_to(R)).as_posix(),(2026,10,20,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.create_system=3;i.external_attr=0o100644<<16
        z.writestr(i,f.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(out)as z:need(z.testzip()is None,'ZIP CRC mismatch')
print(json.dumps({'archive':str(out),'sha256':sha(out),'bytes':out.stat().st_size,'files':len(files)},indent=2))
