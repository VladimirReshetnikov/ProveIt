#!/usr/bin/env python3
"""Literal zero-set chart and degree-budget reconstruction; stdlib only."""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent

def read(p): return json.loads(p.read_text())
def write(p,o): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,sort_keys=True,indent=2)+'\n')
def sha(o):return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(ts):return {tuple(m):c for c,m in ts}
def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
 out={}
 for p in ps:
  for m,c in p.items():out[m]=out.get(m,0)+c
 return {m:c for m,c in out.items() if c}
def scale(c,p):return {m:c*x for m,x in p.items() if c*x}
def mul(p,q):
 out={}
 for m,c in p.items():
  for n,d in q.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def sub(p,mp):
 out={}
 for mon,c in p.items():
  t={():c}
  for v in mon:t=mul(t,mp.get(v,{(v,):1}))
  out=add(out,t)
 return out
def finish(e):
 rows=[load(r['terms']) for r in e['residuals']];P=add(*[mul(r,r) for r in rows]);d=max(map(len,P));e['metrics']={'variables':len(e['variables']),'quadratic_rows' if d<=4 else 'residual_rows':len(rows),'exact_degree':d,'expanded_monomials':len(P),'max_abs_expanded_coefficient':max(map(abs,P.values())),'max_abs_row_coefficient':max(abs(c) for r in rows for c in r.values())}
 return {'schema':'sparse_integer_polynomial_v1','domain':e['domain'],'variables':len(e['variables']),'terms':dump(P)}
def chart():
 src=read(ROOT/'inherited/inherited/pooled202/equation.json');cert=read(ROOT/'chart202/certificate.json');G={int(v):load(p) for v,p in cert['inverse_map'].items()};rows=[sub(load(r['terms']),G) for r in src['residuals']]
 for i,j,k in cert['row_operations']:rows[i]=add(rows[i],scale(k,rows[j]))
 e=deepcopy(src);e['residuals']=[{'label':'round23.gatechart.s'+str(j),'terms':dump(p)} for j,p in enumerate(rows)];e['variant']='round23_natural202_certified_affine_chart';ex=finish(e)
 if sha(e)!=cert['target_sha256']:raise ValueError('chart reconstruction digest')
 return e,ex

def contract(source,cert,name):
 if sha(source)!=cert['source_sha256']:raise ValueError('contraction source digest')
 e=deepcopy(source);rows=[load(r['terms'])for r in e['residuals']];labels=[r['label']for r in e['residuals']];kept=list(range(len(e['variables'])))
 for op in cert['operations']:
  v=op['variable'];j=op['row'];r=rows[j];a=r.get((v,),0)
  if abs(a)!=1 or any(v in m for m in r if m!=(v,)):raise ValueError('not a monic definition')
  f=scale(-a,add(r,{(v,):-a}))
  if dump(f)!=op['definition']:raise ValueError('recorded definition mismatch')
  rows=[sub(p,{v:f}) for k,p in enumerate(rows) if k!=j];labels.pop(j);kept.remove(v)
 if kept!=cert['retained_indices']:raise ValueError('retained indices')
 ren={v:i for i,v in enumerate(kept)};e['variables']=[e['variables'][v]for v in kept];e['residuals']=[{'label':s,'terms':dump({tuple(ren[v]for v in m):c for m,c in r.items()})}for r,s in zip(rows,labels)];e['variant']='round23_'+name;ex=finish(e)
 return e,ex

def main(out):
 e,x=chart();write(out/'chart202/equation.json',e);write(out/'chart202/expanded_polynomial.json',x);summary={'chart202':e['metrics']}
 for name,config in read(ROOT/'PROFILES.json').items():
  source=e if config['source']=='chart202' else read(ROOT/config['source']/'equation.json');cert=read(ROOT/name/'contractions.json');ee,xx=contract(source,cert,name);write(out/name/'equation.json',ee);write(out/name/'expanded_polynomial.json',xx);summary[name]=ee['metrics']
 write(out/'SUMMARY.json',summary);print(json.dumps(summary,sort_keys=True,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);main(ap.parse_args().output)
