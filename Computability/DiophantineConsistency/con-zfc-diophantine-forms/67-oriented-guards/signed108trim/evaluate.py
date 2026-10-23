#!/usr/bin/env python3
"""Modular evaluation of the literal fixed polynomial; not a solution test."""
from pathlib import Path
from functools import reduce
import argparse,gzip,json
R=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--modulus',type=int,default=1000003);p.add_argument('values',type=int,nargs=10);a=p.parse_args()
if a.modulus<2:p.error('modulus must be at least 2')
body=json.loads((R/'generated/sun10.json').read_text());records=json.loads((R/'generated/source_records.json').read_text())
ports=[int.from_bytes(gzip.decompress((R/'data'/(f+'.bin.gz')).read_bytes()),'little') for f in ['beta','K','MC','MF_source']]
fixed={name:sum(row['coefficient']*reduce(lambda x,y:x*y,(pow(v,e,a.modulus) for v,e in zip(ports,row['powers'])),1) for row in rows)%a.modulus for name,rows in records['recipes'].items()}
fixed.update(beta_source=pow(2,2134940,a.modulus),beta_mask=pow(2,2134917,a.modulus));vv=dict(zip(body['variables'],a.values));out=[]
for n in body['nodes']:
 k=n['kind']
 if k=='literal':v=n['value']
 elif k=='fixed':v=fixed[n['name']]
 elif k=='variable':v=vv[n['name']]
 else:
  x,y=out[n['left']],out[n['right']];v=x+y if k=='add' else x-y if k=='sub' else x*y
 out.append(v%a.modulus)
print(json.dumps({'modulus':a.modulus,'residue':out[body['output']],'variable_order':body['variables']}))
