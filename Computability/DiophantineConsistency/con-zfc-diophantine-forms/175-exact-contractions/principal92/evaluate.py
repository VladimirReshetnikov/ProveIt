#!/usr/bin/env python3
"""Evaluate the literal polynomial, or restore its eliminated coordinates.

This evaluates a supplied tuple. It does not search for zeros or decide
consistency. Only Python integer arithmetic is used.
"""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
def sparse_eval(ts,values):
 result=0
 for c,mon in ts:
  for v in mon:c*=values[v]
  result+=c
 return result
def circuit_eval(circuit,values):
 require_input(values,circuit['input_count']);out=[]
 for node in circuit['nodes']:
  if node[0]=='const':v=node[1]
  elif node[0]=='input':v=values[node[1]]
  elif node[0]=='add':v=out[node[1]]+out[node[2]]
  elif node[0]=='sub':v=out[node[1]]-out[node[2]]
  elif node[0]=='mul':v=out[node[1]]*out[node[2]]
  else:raise ValueError('unknown polynomial operation')
  out.append(v)
 return out[circuit['output']],[out[i] for i in circuit['residual_outputs']]
def require_input(x,n):
 if type(x)is not list or len(x)!=n or any(type(v)is not int for v in x):raise ValueError(f'exactly {n} integers required')
def restore191(values,source,cert):
 require_input(values,92);memo=dict(zip(cert['free_source_variables'],values));definitions={s['variable']:s['restoration_source_terms'] for s in cert['steps']};visiting=set()
 def get(v):
  if v in memo:return memo[v]
  if v in visiting:raise ValueError('cyclic certificate')
  visiting.add(v);out=0
  for c,mon in definitions[v]:
   for u in mon:c*=get(u)
   out+=c
  visiting.remove(v);memo[v]=out;return out
 return [get(v) for v in range(len(source['variables']))]
def restore220(values191,source220,bridge):
 gone={s['variable'] for s in bridge['steps']};keep=[v for v in range(len(source220['variables'])) if v not in gone];vals={v:x for v,x in zip(keep,values191)}
 for step in reversed(bridge['steps']):vals[step['variable']]=sparse_eval(step['restoration'],vals)
 return [vals[v] for v in range(len(source220['variables']))]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('tuple',help='JSON list file, or - for stdin');g=p.add_mutually_exclusive_group();g.add_argument('--residuals',action='store_true');g.add_argument('--restore191',action='store_true');g.add_argument('--restore220',action='store_true');p.add_argument('--project220',action='store_true',help='instead project a supplied 220-coordinate tuple to 92 coordinates');a=p.parse_args()
 if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
 values=json.loads(sys.stdin.read() if a.tuple=='-' else Path(a.tuple).read_text());cert=json.loads((ROOT/'projection92.json').read_text());source=json.loads((ROOT/'sources/source191.json').read_text());source220=json.loads((ROOT/'sources/source220.json').read_text());bridge=json.loads((ROOT/'sources/bridge191.json').read_text())
 if a.project220:
  require_input(values,220);gone={s['variable'] for s in bridge['steps']};keep=[v for v in range(220) if v not in gone];result=[values[keep[i]] for i in cert['free_source_variables']]
 elif a.restore191 or a.restore220:
  result=restore191(values,source,cert)
  if a.restore220:result=restore220(result,source220,bridge)
 else:
  circuit=json.loads((ROOT/'circuit92.json').read_text());value,residuals=circuit_eval(circuit,values);result=residuals if a.residuals else value
 print(json.dumps(result))
if __name__=='__main__':main()
