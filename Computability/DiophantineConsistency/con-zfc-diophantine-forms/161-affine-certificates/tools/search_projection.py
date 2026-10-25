#!/usr/bin/env python3
"""Search exact degree-preserving monic eliminations modulo retained gate rows."""
from collections import Counter
from pathlib import Path
import json,sys

def clean(p):return {m:c for m,c in p.items() if c}
def add(a,b,k=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+k*c
 return clean(d)
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   q=tuple(sorted(m+n));d[q]=d.get(q,0)+c*e
 return clean(d)
def sub(p,v,a):
 d={}
 for m,c in p.items():
  x={():c}
  for i in m:x=mul(x,a if i==v else {(i,):1})
  d=add(d,x)
 return d
def divide(m,n):
 m=list(m)
 for i in n:
  if i not in m:return None
  m.remove(i)
 return tuple(m)
def emit(p):return [[c,list(m)] for m,c in sorted(p.items())]

def attempt(rows,ri,v):
 r=rows[ri];co=r[(v,)]
 a={m:-co*c for m,c in r.items() if m!=(v,)}
 out=[sub(p,v,a) for p in rows]
 if out[ri]:raise ValueError('bad pivot')
 reducers=[]
 for j,p in enumerate(rows):
  if j==ri or any(v in m for m in p):continue
  quads=[(m,c) for m,c in p.items() if len(m)==2]
  if len(quads)==1 and abs(quads[0][1])==1:reducers.append((j,p,*quads[0]))
 ops=[]
 for i,p in enumerate(out):
  if i==ri:continue
  while max(map(len,p),default=0)>2:
   m=max(p,key=lambda m:(len(m),m));co=p[m]
   found=False
   for j,r,n,c in reducers:
    if j==i:continue
    q=divide(m,n)
    if q is None:continue
    h={q:co*c};p=add(p,mul(h,r),-1);ops.append((i,j,emit(h)));found=True;break
   if not found:return None
  out[i]=p
 return out,a,ops

def main(path):
 d=json.loads(Path(path).read_text());rows=[{tuple(m):c for c,m in r['terms']} for r in d['residuals']]
 candidates=[]
 for ri,p in enumerate(rows):
  for m,c in p.items():
   if len(m)!=1 or abs(c)!=1:continue
   v=m[0]
   if any(v in n for n in p if n!=m):continue
   out=attempt(rows,ri,v)
   if out:
    nr,a,ops=out
    candidates.append({'row':ri,'v':v,'name':d['variables'][v]['name'],'replacement':emit(a),'operations':ops,'row_support':sum(len(p) for p in nr)})
 print(json.dumps({'source':path,'variables':len(d['variables']),'rows':len(rows),'candidates':candidates},indent=2))
if __name__=='__main__':main(sys.argv[1])
