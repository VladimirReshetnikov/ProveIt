#!/usr/bin/env python3
"""Verify ordered chunks reconstruct the exact pinned whole-row bytes."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign14-prefix-formula/row00.prefix';raw=src.read_bytes();h=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((P/'manifest.json').read_text())
assert h(raw)==m['source_sha256']=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and len(raw)==m['source_length']==689
parts=[]
for i,row in enumerate(m['chunks']):
 assert row['file']==f'chunk{i:02}.prefix';b=(P/row['file']).read_bytes();assert b and len(b)==row['length'] and h(b)==row['sha256'];parts.append(b)
assert parts[0]==b'-*+++*j+*B+b11*B+b1' and b''.join(parts)==raw
print('PASS: ordered short chunks reconstruct exact pinned row00 bytes')
