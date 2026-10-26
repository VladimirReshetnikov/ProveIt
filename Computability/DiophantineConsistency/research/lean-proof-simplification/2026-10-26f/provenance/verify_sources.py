#!/usr/bin/env python3
"""Verify selected pinned source bytes without network access."""
import pathlib,json,hashlib,sys
BASE=pathlib.Path(__file__).resolve().parents[1]
m=json.load(open(BASE/'provenance/source_manifest.json')); errors=[]
for f in m['sources']:
 p=BASE/'sources'/f['path']
 if not p.is_file():errors.append(f['path']+': missing');continue
 d=p.read_bytes()
 checks=(len(d)==f['size'],hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==f['sha'],hashlib.sha256(d).hexdigest()==f['sha256'])
 if not all(checks):errors.append(f['path']+': mismatch')
print(json.dumps({'commit':m['commit'],'files':len(m['sources']),'errors':errors},indent=2));sys.exit(bool(errors))
