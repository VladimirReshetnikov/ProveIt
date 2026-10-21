#!/usr/bin/env python3
"""Recover the sixteen unchanged beam finalists from portable gzip records."""
import argparse,gzip,hashlib,json
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if a.output.exists():raise SystemExit('Refusing an existing output directory')
 source=a.packet/'rotate-x-additive-run1';report=json.loads((source/'result.json').read_text());items=[]
 for row in report['finalists']:
  name=row['source'];assert Path(name).name==name and name.endswith('.json')
  raw=gzip.decompress((source/(name+'.gz')).read_bytes());assert hashlib.sha256(raw).hexdigest()==row['sha256']
  data=json.loads(raw);assert len(data)==4738 and all(len(x)==3 for x in data)
  items.append((name,raw))
 assert len(items)==16 and len({n for n,_ in items})==16
 a.output.mkdir(parents=True)
 for name,raw in items:(a.output/name).write_bytes(raw)
 (a.output/'result.json').write_bytes((source/'result.json').read_bytes())
 print('PASS: 16 exact source byte strings restored; no checker, allocator or machine invoked.')
if __name__=='__main__':main()
