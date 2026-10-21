#!/usr/bin/env python3
from pathlib import Path
import argparse,json,gzip,hashlib
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=False)
r=json.loads((a.input/'result.json').read_text())
for e in r['finalists']:
 data=gzip.decompress((a.input/(e['source']+'.gz')).read_bytes())
 assert hashlib.sha256(data).hexdigest()==e['sha256']
 (a.output/e['source']).write_bytes(data)
print(json.dumps({'restored':len(r['finalists']),'all_sha256_match':True}))
