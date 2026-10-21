#!/usr/bin/env python3
"""Unpack pinned scanner research inputs into the requested work directory."""
from pathlib import Path
import argparse,gzip,hashlib,json
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
here=Path(__file__).resolve().parent;data=json.loads((here/'provenance.json').read_text());a.out.mkdir(parents=True,exist_ok=True)
for item in data['files']:
    packed=(here/item['packed']).read_bytes();assert hashlib.sha256(packed).hexdigest()==item['packed_sha256']
    raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==item['unpacked_sha256']
    (a.out/item['unpacked']).write_bytes(raw)
print(json.dumps({'status':'SCANNER_INPUTS_UNPACKED','files':len(data['files'])},indent=2))
