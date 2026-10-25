#!/usr/bin/env python3
"""Rebuild the fixed 13-input norm chart, no external commands or proof search."""
import argparse,json
from pathlib import Path
from circuit import DAG,export
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
TAG='integer13_degree152_ops119'
def build():
 s=json.loads((ROOT/(TAG+'_spec.json')).read_text());d=DAG(s['variables'])
 e={v:d.leaf('variable',v) for v in s['variables']};e.update({v:d.leaf('coefficient',v) for v in PORTS})
 for n,f in s['registers']:e[n]=eval(f,{'__builtins__':{}},e)
 p=export(TAG,d,e['P'],{n:e[n] for n,f in s['registers']},{'exact_degree':152,'fixed_numerals':PORTS,'proof':'PROOF.md','proof_status':'Ordinary universal polynomial shear; retained signed native/refutation theorem. No new kernel certificate.'})
 p['coefficient_binding']='inherited/coefficients/BINDING.json'
 return p
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();p=build()
 for name,obj in [(TAG+'.json',p),('METRICS.json',[{k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']}])]:
  data=json.dumps(obj,indent=2,sort_keys=True)+'\n';path=ROOT/name
  if args.check:
   if path.read_text()!=data:raise ValueError('Rebuild mismatch '+name)
  else:path.write_text(data)
 print(json.dumps({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']}))
