#!/usr/bin/env python3
"""Reconstruct the eight fixed polynomial circuits and their six source pools."""
import argparse,hashlib,json,copy,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
pool=module('pool_build',ROOT/'code/build_pooling.py');projection=module('projection_build',ROOT/'inherited/build_projections_original.py')
def load(p):return json.loads(p.read_bytes())
def enc(a):return(json.dumps(a,sort_keys=True,separators=(',',':'))+'\n').encode()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if a.output.exists():raise ValueError('output directory must not already exist')
 a.output.mkdir(parents=True)
 for anchor in ['linear219','linear221']:
  anum=int(anchor[-3:]);up=ROOT/'upstream173/source'/('anchor'+str(anum));pool.SOURCE=up/'equation.json';parent=load(pool.SOURCE);cert=load(up/'certificate.json');nmin=128 if anum==221 else 16
  row=next(r for r in parent['residuals'] if r['label']=='cofinal.horizon');v=next(i for i,x in enumerate(parent['variables']) if x['name']=='cofinal.horizon_root')
  row['terms']=pool.serial(pool.add(pool.add(pool.var(0),pool.scale(pool.var(v),-2*nmin)),pool.con(-nmin)))
  parent['variables'][v]['name']='cofinal.horizon_parameter';parent['schema']='conzfc-signed-cofinal-anchor-v1';parent['semantic_transform']='t = tmin*(2*z+1); positivity recovered from powers'
  dest=a.output/'sources'/anchor;dest.mkdir(parents=True);(dest/'signed_anchor_parent.json').write_bytes(enc(parent))
  for variant in ['all5','staged','paired']:
   e,c,m=pool.construct(parent,variant,cert);d=dest/variant;d.mkdir()
   for fn,obj in [('equation.json',e),('certificate.json',c),('metrics.json',m)]: (d/fn).write_bytes(enc(obj))
 (a.output/'equations').mkdir()
 for cp in sorted((ROOT/'certificates').glob('*.json')):
  c=load(cp);b=a.output/'sources'/c['anchor']/c['variant'];raw=(b/'equation.json').read_bytes();e=projection.build(json.loads(raw),load(b/'certificate.json'),c,hashlib.sha256(raw).hexdigest());(a.output/'equations'/cp.name).write_bytes(enc(e))
 files=list((a.output/'sources').rglob('*.json'))+list((a.output/'equations').glob('*.json'))
 for f in files:
  if f.read_bytes()!=(ROOT/f.relative_to(a.output)).read_bytes():raise ValueError('Reconstruction differs: '+str(f))
 print(json.dumps({'status':'PASS','files_reconstructed_byte_identically':len(files),'output':str(a.output.resolve())}))
if __name__=='__main__':main()
