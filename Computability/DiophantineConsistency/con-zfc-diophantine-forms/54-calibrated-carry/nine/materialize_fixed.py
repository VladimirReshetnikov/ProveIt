#!/usr/bin/env python3
"""Materialize every live fixed leaf, deduplicated by sign and magnitude."""
from pathlib import Path
import json,gzip,hashlib
ROOT=Path(__file__).resolve().parent

def need(c,m):
 if not c:raise ValueError(m)
def main():
 native=json.loads((ROOT.parent/'native/COEFFICIENT_BINDING.json').read_text());ports={}
 for name,file in native['binding'].items():
  raw=gzip.decompress((ROOT.parent/'native'/file).read_bytes());v=int.from_bytes(raw,'little')
  record=next(r for r in native['ports']if r['name']=={'K0':'K','MF':'MF_source'}.get(name,name));need(hashlib.sha256(raw).hexdigest()==record['sha256'],'Native hash')
  ports[name]=v
 directory=ROOT/'fixed';directory.mkdir(exist_ok=True);circuits={};leaves={}
 for path in sorted((ROOT/'generated').glob('nine_*.json')):
  obj=json.loads(path.read_text());recipes={r['name']:r['terms']for r in obj['coefficient_recipes']};mapleaves={}
  for name in sorted(set(n['name']for n in obj['nodes']if n['kind']=='fixed')):
   if name in obj['fixed_power_leaves']:
    exponent=obj['fixed_power_leaves'][name];value=1<<exponent;definition=dict(power_of_two=exponent)
   else:
    recipe=recipes[name];value=sum(t['coefficient']*__import__('functools').reduce(lambda a,b:a*b,(ports[p]**e for p,e in zip(['beta','K0','MC','MF'],t['powers'])),1)for t in recipe);definition=dict(port_order=['beta','K0','MC','MF'],terms=recipe)
   sign=-1 if value<0 else 1;value=abs(value);raw=value.to_bytes(max(1,(value.bit_length()+7)//8),'little');digest=hashlib.sha256(raw).hexdigest();key=('negative_'if sign<0 else'positive_')+digest
   file=f'{digest}.bin.gz';packed=gzip.compress(raw,mtime=0);(directory/file).write_bytes(packed)
   leaves[key]=dict(sign=sign,bits=value.bit_length(),bytes=len(raw),file='fixed/'+file,magnitude_sha256=digest,gzip_sha256=hashlib.sha256(packed).hexdigest(),definition=definition)
   mapleaves[name]=key
  circuits[path.name]=dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),fixed_leaves=mapleaves)
 out=dict(schema='round8-nine-materialized-fixed-leaves-v1',encoding='sign times unsigned little-endian integer magnitude, gzip compressed; zero convention sign+1,one zero byte',native_binding='../native/COEFFICIENT_BINDING.json',native_binding_sha256=hashlib.sha256((ROOT.parent/'native/COEFFICIENT_BINDING.json').read_bytes()).hexdigest(),distinct_signed_values=len(leaves),circuits=circuits,leaves=leaves)
 (ROOT/'FIXED_BINDING.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(circuits=len(circuits),distinct_signed_values=len(leaves),compressed_files=len(list(directory.glob('*.gz')))),indent=2))
if __name__=='__main__':main()
