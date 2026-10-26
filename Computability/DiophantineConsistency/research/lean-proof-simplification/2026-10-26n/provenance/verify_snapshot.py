#!/usr/bin/env python3
"""Offline byte-integrity replay. Does not claim Lean elaboration."""
import hashlib,json,pathlib,sys
base=pathlib.Path(__file__).resolve().parents[1]
m=json.loads((base/'provenance/source_manifest.json').read_text())
bad=[]
for f in m['sources']:
 p=base/'sources'/f['path']
 if not p.is_file(): bad.append([f['path'],'missing']);continue
 d=p.read_bytes()
 got=hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
 if got!=f['sha'] or hashlib.sha256(d).hexdigest()!=f['sha256']:
  bad.append([f['path'],'hash mismatch'])
print(json.dumps({'commit':m['commit'],'checked':len(m['sources']),'failures':bad},indent=2))
sys.exit(bool(bad))
