#!/usr/bin/env python3
"""Fetch the exact selected manifest, validate Git blobs + SHA256, preserve files."""
import pathlib,json,hashlib,urllib.request,concurrent.futures
BASE=pathlib.Path(__file__).resolve().parents[1]
m=json.load(open(BASE/'provenance/source_manifest.json'))
def fetch(f):
 p=BASE/'sources'/f['path'];d=p.read_bytes() if p.exists() else urllib.request.urlopen(f['url'],timeout=90).read()
 assert len(d)==f['size'],f['path']
 assert hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==f['sha'],f['path']
 assert hashlib.sha256(d).hexdigest()==f['sha256'],f['path']
 p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists():p.write_bytes(d)
 return f['path']
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
 for i,p in enumerate(ex.map(fetch,m['sources']),1):
  if i%100==0:print(i,p,flush=True)
print('Verified',len(m['sources']),'files at',m['commit'])
