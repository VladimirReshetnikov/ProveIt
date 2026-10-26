"""Small exact sparse-polynomial kernel for the literal pooling producers."""
import json
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def ser(p):return [[c,list(m)]for m,c in sorted(p.items())if c]
def poly(t):return {tuple(m):c for c,m in t}
def add(a,b,k=1):
 d=a.copy()
 for m,c in b.items():
  d[m]=d.get(m,0)+k*c
  if not d[m]:del d[m]
 return d
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items()if c}
def degree(p):return max(map(len,p),default=0)
