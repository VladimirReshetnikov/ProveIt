#!/usr/bin/env python3
import hashlib,json,sys,subprocess
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-row00-chunks';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'manifest.json')=='053f24f7ee05853d311545145e3353cb19bf3de304978cfdefcbbf3067b7ba64' and sha(p/'check.py')=='3846a438f8d5c25d7c50f9a3f1f087c23bfd6317f74741aaddd27ceed991cb0d'
m=json.loads((p/'manifest.json').read_text());raw=(root/'research/nine-sharing-sign14-prefix-formula/row00.prefix').read_bytes();assert len(raw)==m['source_length']==689 and hashlib.sha256(raw).hexdigest()==m['source_sha256']=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6';assert len(m['chunks'])==22
parts=[]
for i,e in enumerate(m['chunks']):
 q=p/f'chunk{i:02}.prefix';b=q.read_bytes();assert e['file']==q.name and e['length']==len(b) and e['sha256']==sha(q) and all(x<128 for x in b) and (len(b)==19 if i==0 else 0<len(b)<=32);parts.append(b)
assert parts[0]==b'-*+++*j+*B+b11*B+b1' and b''.join(parts)==raw
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,check=True,timeout=120);assert not x.stderr and x.stdout.strip()=='PASS: ordered short chunks reconstruct exact pinned row00 bytes'
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','chunks':22,'bytes':689,'first':19,'scope':'external ordered file concatenation; no Lean full-file/JSON/PDF theorem'},indent=2))
