#!/usr/bin/env python3
"""Deterministic fixed arithmetic circuits, standard library only."""
import argparse,json
from pathlib import Path
from circuit import DAG,export
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def build(tag):
 s=json.loads((ROOT/(tag+'_spec.json')).read_text());d=DAG(s['variables'])
 e={v:d.leaf('variable',v) for v in s['variables']};e.update({v:d.leaf('coefficient',v) for v in PORTS})
 for n,f in s['registers']:e[n]=eval(f,{'__builtins__':{}},e)
 p=export(tag,d,e['P'],{n:e[n] for n,f in s['registers']},{'exact_degree':s['degree'],'fixed_numerals':PORTS,'proof':'PROOF.md','proof_status':'Ordinary guarded quadratic trace resultant and unweighted root merger; inherited native/refutation calibration. No new kernel certificate.'})
 p['coefficient_binding']='inherited_round22/inherited_round20/inherited/coefficients/BINDING.json'
 return p
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args();metrics=[]
 for tag in ['integer13_degree118','integer13_degree120']:
  p=build(tag);metrics.append({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']})
  data=json.dumps(p,indent=2,sort_keys=True)+'\n';path=ROOT/(tag+'.json')
  if args.check:
   if path.read_text()!=data:raise ValueError('Rebuild mismatch '+tag)
  else:path.write_text(data)
 data=json.dumps(metrics,indent=2,sort_keys=True)+'\n';path=ROOT/'METRICS.json'
 if args.check:
  if path.read_text()!=data:raise ValueError('metric mismatch')
 else:path.write_text(data)
 print(data)
