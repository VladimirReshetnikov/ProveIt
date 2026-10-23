#!/usr/bin/env python3
"""Materialize all live fixed leaves; no search or truth-dependent choice."""
from pathlib import Path
import gzip,hashlib,json
ROOT=Path(__file__).resolve().parent
def j(path):return json.loads((ROOT/path).read_text())
def main():
 ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients/payloads'/f'{n}.bin.gz').read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
 def evaluate(recipe):
  value=0
  for t in recipe:
   v=t['coefficient']
   for p,e in zip(ports,t['powers']):v*=p**e
   value+=v
  return value
 c10=j('data/polynomial.json');r10=j('data/coefficient_recipes.json');c9=j('nine/generated/multitarget_nine_positive.json')
 recipes9={r['name']:r['terms'] for r in c9['coefficient_recipes']};manifest={}
 for label,circuit in [('signed10',c10),('positive9',c9)]:
  entries=[];dest=ROOT/'fixed'/label;dest.mkdir(parents=True,exist_ok=True)
  for name in sorted({n['name'] for n in circuit['nodes'] if n['kind']=='fixed'}):
   if name=='beta_source':recipe={'power_of_two':r10['beta_source_exponent']};value=1<<recipe['power_of_two']
   elif name=='base_floor':recipe={'power_of_two':c9['base_floor_exponent']};value=1<<recipe['power_of_two']
   else:recipe=r10['recipes'][name] if label=='signed10' else recipes9[name];value=evaluate(recipe)
   raw=bytes([int(value<0)])+abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'little')
   encoded=gzip.compress(raw,mtime=0);p=dest/(name+'.bin.gz');p.write_bytes(encoded)
   entries.append({'name':name,'file':str(p.relative_to(ROOT)),'encoding':'gzip of one sign byte then unsigned little-endian magnitude','raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(encoded).hexdigest(),'bits':abs(value).bit_length(),'recipe':recipe})
  manifest[label]=entries
 (ROOT/'fixed/FIXED_LEAVES.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({k:len(v) for k,v in manifest.items()}))
if __name__=='__main__':main()
