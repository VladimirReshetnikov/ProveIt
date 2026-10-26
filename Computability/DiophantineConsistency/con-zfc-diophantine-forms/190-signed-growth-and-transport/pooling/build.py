#!/usr/bin/env python3
"""Rebuild all exact source pools and final circuits without a search."""
import json,importlib.util,pathlib,hashlib,argparse
ROOT=pathlib.Path(__file__).resolve().parent
def module(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def load(p):return json.loads(p.read_bytes())
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,required=True);a=ap.parse_args()
 if a.output.exists():raise ValueError('output must be a fresh directory')
 a.output.mkdir(parents=True);pool=module('four_base_pool',ROOT/'code/build_pooling.py');proj=module('circuit_builder',ROOT/'inherited/build_projections_original.py');pool.SOURCE=ROOT/'source/pell216.json'
 parent=load(pool.SOURCE);parent['residuals'][131]['terms']=pool.serial(pool.add(pool.add(pool.var(0),pool.scale(pool.var(184),-4)),pool.con(-2)));parent['variables'][184]['name']='cofinal.horizon_parameter';parent['schema']='signed-pell-growth-v1'
 (a.output/'source').mkdir();(a.output/'source/signed216.json').write_bytes(pool.canonical(parent))
 for variant in ['staged','all4']:
  e,c,m=pool.construct(parent,variant,None);dest=a.output/'sources'/variant;dest.mkdir(parents=True)
  for fn,o in [('equation.json',e),('certificate.json',c),('metrics.json',m)]:(dest/fn).write_bytes(pool.canonical(o))
 (a.output/'equations').mkdir()
 for cp in sorted((ROOT/'certificates').glob('*.json')):
  profile=load(cp);p=a.output/'sources'/profile['variant'];raw=(p/'equation.json').read_bytes();out=proj.build(json.loads(raw),load(p/'certificate.json'),profile,hashlib.sha256(raw).hexdigest());(a.output/'equations'/cp.name).write_bytes(pool.canonical(out))
 files=sorted(a.output.rglob('*.json'))
 for f in files:
  original=ROOT/f.relative_to(a.output)
  if f.read_bytes()!=original.read_bytes():raise ValueError('byte mismatch: '+str(f))
 print(json.dumps({'status':'PASS','byte_identical_json_files':len(files),'output':str(a.output.resolve())}))
if __name__=='__main__':main()
