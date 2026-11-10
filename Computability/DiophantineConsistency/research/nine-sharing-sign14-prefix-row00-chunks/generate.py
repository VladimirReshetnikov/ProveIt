#!/usr/bin/env python3
"""Split the pinned row00 prefix into short, exactly concatenated byte files."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign14-prefix-formula/row00.prefix'
h=lambda b:hashlib.sha256(b).hexdigest();raw=src.read_bytes()
assert h(raw)=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and len(raw)==689
assert raw[:19]==b'-*+++*j+*B+b11*B+b1'
chunks=[raw[:19]]+[raw[i:i+32] for i in range(19,len(raw),32)];rows=[]
for i,data in enumerate(chunks):
 p=P/f'chunk{i:02}.prefix';p.write_bytes(data);rows.append({'file':p.name,'length':len(data),'sha256':h(data)})
(P/'manifest.json').write_text(json.dumps({'source_sha256':h(raw),'source_length':len(raw),'chunks':rows},sort_keys=True,indent=2)+'\n')
print(json.dumps({'status':'GENERATED','chunks':len(rows),'source_length':len(raw)}))
