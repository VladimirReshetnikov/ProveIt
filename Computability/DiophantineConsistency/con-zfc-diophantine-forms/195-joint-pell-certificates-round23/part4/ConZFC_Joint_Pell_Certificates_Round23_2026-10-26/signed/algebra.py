#!/usr/bin/env python3
"""Minimal producer sparse arithmetic; the verifier does not import this module."""
import json,hashlib,copy,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def read(p):return json.loads(p.read_text())
def need(x,s):
 if not x:raise ValueError(s)
def clean(x):return {m:c for m,c in x.items() if c}
def poly(ts):
 p={}
 for c,m in ts:
  t=tuple(sorted(m));p[t]=p.get(t,0)+c
 return clean(p)
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def add(a,b,k=1):
 p=a.copy()
 for m,c in b.items():p[m]=p.get(m,0)+k*c
 return clean(p)
def mul(a,b):
 p={}
 for m,c in a.items():
  for n,d in b.items():
   t=tuple(sorted(m+n));p[t]=p.get(t,0)+c*d
 return clean(p)
def subst(p,v,f):
 out={}
 for m,c in p.items():
  a={():c}
  for t in m:a=mul(a,f if t==v else {(t,):1})
  out=add(out,a)
 return out

def compact(e,rows):
 used=sorted({v for p in rows for m in p for v in m});ren={v:i for i,v in enumerate(used)}
 return {'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','variables':[e['variables'][v] for v in used], 'residuals':[{'label':f'R{j}','terms':terms({tuple(ren[v] for v in m):c for m,c in p.items()})} for j,p in enumerate(p for p in rows if p)]}
def result(e):
 p={}
 for r in e['residuals']:
  q=poly(r['terms']);p=add(p,mul(q,q))
 metrics=dict(variables=len(e['variables']),rows=len(e['residuals']),degree=max(map(len,p)),monomials=len(p),height=max(map(abs,p.values())),row_height=max(abs(c) for r in e['residuals'] for c,m in r['terms']))
 return dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=len(e['variables']),terms=terms(p)),metrics
