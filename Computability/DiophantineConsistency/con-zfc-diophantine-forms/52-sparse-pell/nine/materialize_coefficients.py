#!/usr/bin/env python3
"""Bind all live fixed leaves to the single audited four-port tuple."""
from pathlib import Path
import json,gzip,hashlib
ROOT=Path(__file__).resolve().parent

def main():
 binding=json.loads((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_text());ports=[]
 for r in binding['ports']:
  raw=(ROOT.parent/'coefficients'/r['file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==r['sha256'];ports.append(int.from_bytes(raw,'little'))
 objects=[json.loads(p.read_text()) for p in sorted((ROOT/'generated').glob('nine_*_positive.json'))];obj=objects[0]
 live=set().union(*({n['name'] for n in o['nodes'] if n['kind']=='fixed'} for o in objects));recipes={}
 for o in objects:
  for r in o['coefficient_recipes']:
   assert r['name'] not in recipes or recipes[r['name']]==r['terms']
   recipes[r['name']]=r['terms']
 out=ROOT/'generated/fixed';out.mkdir(exist_ok=True);records=[]
 for name in sorted(live):
  if name=='radix_scale':value=1<<obj['radix_scale_exponent'];rec={'power_of_two':obj['radix_scale_exponent']}
  else:
   value=0;rec=recipes[name]
   for term in rec:
    a=term['coefficient']
    for p,e in zip(ports,term['powers']):a*=p**e
    value+=a
  raw=bytes([int(value<0)])+abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'little');compressed=gzip.compress(raw,mtime=0);path=out/(name+'.bin.gz');path.write_bytes(compressed)
  records.append({'name':name,'file':str(path.relative_to(ROOT)),'encoding':'gzip of sign byte (0 nonnegative; 1 negative), then unsigned little-endian magnitude','bit_length':abs(value).bit_length(),'raw_bytes':len(raw),'gzip_bytes':len(compressed),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(compressed).hexdigest(),'recipe':rec})
 result={'schema':'round7-nine-materialized-integer-coefficients-v1','binding':'../coefficients/COEFFICIENT_BINDING.json','binding_sha256':hashlib.sha256((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_bytes()).hexdigest(),'coefficient_bound_exponent':obj['coefficient_bound_exponent'],'radix_scale_exponent':obj['radix_scale_exponent'],'fixed_leaves':records,'raw_bytes':sum(r['raw_bytes'] for r in records),'gzip_bytes':sum(r['gzip_bytes'] for r in records),'domain':'nine positive integers or separately translated nine nonnegative integers','proof':'PROOF.md','new_end_to_end_kernel_certificate':False}
 (ROOT/'COEFFICIENT_INSTANCE.json').write_text(json.dumps(result,indent=2)+'\n');print({k:result[k] for k in ['raw_bytes','gzip_bytes']})
if __name__=='__main__':main()
