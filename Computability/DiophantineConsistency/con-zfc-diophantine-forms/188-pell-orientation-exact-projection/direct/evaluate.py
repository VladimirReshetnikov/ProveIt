#!/usr/bin/env python3
"""Evaluate one supplied tuple; never searches for a refutation or zero."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent
def main():
 ap=argparse.ArgumentParser();ap.add_argument('profile');ap.add_argument('tuple',nargs='?');ap.add_argument('--modulus',type=int);ap.add_argument('--variables',action='store_true');ap.add_argument('--residuals',action='store_true');ap.add_argument('--restore',action='store_true');ap.add_argument('--zero',action='store_true');a=ap.parse_args()
 p=Path(a.profile);p=p if p.is_file() else ROOT/'equations'/(a.profile+'.json');g=json.loads(p.read_text())
 if a.variables:print(json.dumps(g['variables'],indent=2));return
 if a.zero:point=[0]*len(g['variables'])
 elif a.tuple:point=json.loads(Path(a.tuple).read_text())
 else:raise SystemExit('Supply a JSON tuple, --zero, or --variables.')
 if not isinstance(point,list) or len(point)!=len(g['variables']) or any(type(x) is not int for x in point):raise SystemExit('Tuple must be a list of exactly the declared number of integers.')
 if a.modulus is not None and a.modulus<2:raise SystemExit('Modulus must be at least two.')
 values=[]
 for nd in g['nodes']:
  op=nd[0]
  if op=='var':v=point[nd[1]]
  elif op=='const':v=nd[1]
  else:
   x,y=(values[i] for i in nd[1:]);v=x+y if op=='+' else x-y if op=='-' else x*y
  values.append(v if a.modulus is None else v%a.modulus)
 result={'value':values[g['output']],'modulus':a.modulus}
 if a.residuals:result['residuals']=[values[i] for i in g['residual_roots']]
 if a.restore:result['restored_source_coordinates']=[values[i] for i in g['restore_source_roots']]
 print(json.dumps(result))
if __name__=='__main__':main()
