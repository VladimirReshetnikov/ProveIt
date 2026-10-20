#!/usr/bin/env python3
"""Recursively verify bundled archive CRC, exact manifests and provenance pins."""
from pathlib import Path,PurePosixPath
from io import BytesIO
from zipfile import ZipFile
import hashlib,json,stat,argparse

def sha(b):return hashlib.sha256(b).hexdigest()
def inspect(raw,label):
 with ZipFile(BytesIO(raw))as z:
  names=z.namelist();assert len(names)==len(set(names));assert z.testzip()is None
  for i in z.infolist():
   p=PurePosixPath(i.filename);assert not p.is_absolute()and'..'not in p.parts and'\\'not in i.filename
   assert stat.S_IFMT(i.external_attr>>16)in(0,stat.S_IFREG,stat.S_IFDIR)and not i.flag_bits&1
  files={n:z.read(n)for n in names if not n.endswith('/')}
  manifests=[]
  for n,body in files.items():
   if n.rsplit('/',1)[-1]=='MANIFEST.sha256':
    prefix=n.rsplit('/',1)[0]+'/';entries={}
    for line in body.decode().splitlines():
     h,p=line.split(None,1);p=p.strip();assert p not in entries;entries[p]=h
     assert sha(files[prefix+p])==h,(label,n,p)
    assert{n[len(prefix):]for n in files if n.startswith(prefix)and n!=prefix+'MANIFEST.sha256'}==set(entries),(label,'manifest inventory')
    manifests.append(dict(path=n,verified_files=len(entries),exact_inventory=True))
  for n,body in files.items():
   if n.endswith('/portable/manifest.json'):
    d=json.loads(body);prefix=n.rsplit('/',1)[0]+'/'
    entries=d['files'];entries={e['path']:e for e in entries}if isinstance(entries,list)else entries
    for p,e in entries.items():
     b=files[prefix+p];expected=e['sha256']if isinstance(e,dict)else e
     assert sha(b)==expected,(label,n,p)
     if isinstance(e,dict):assert len(b)==e['size']
    assert{n[len(prefix):]for n in files if n.startswith(prefix)and n!=prefix+'manifest.json'}==set(entries),(label,'portable manifest inventory')
    manifests.append(dict(path=n,verified_files=len(entries),exact_inventory=True))
  nested=[inspect(b,label+'!'+n)for n,b in files.items()if n.endswith('.zip')]
  return dict(archive=label,sha256=sha(raw),bytes=len(raw),members=len(files),crc_pass=True,manifests=manifests,nested=nested)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('archive',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args();r=inspect(a.archive.read_bytes(),a.archive.name);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
