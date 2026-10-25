#!/usr/bin/env python3
"""Replay frozen Round19 common-sphere integer transformations (stdlib only)."""
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
def initial():
 e=copy.deepcopy(read(ROOT/'sources/common252.json'));tr=read(ROOT/'sources/common252_translation.json'); ns={v['name']:i for i,v in enumerate(e['variables'])};q=ns['pow2.output'];s=dict(tr['shifts']).get(q,0);z=len(e['variables']);e['variables'].append({'name':'radix.odd_square_root','kind':'signed_witness'})
 rs=[]
 for r in e['residuals']:
  if r['label']=='domain_guard.2':continue
  p=poly(r['terms'])
  if r['label']=='domain_guard.4':
   need(p.get(())==-1 and sum(c==-4 for c in p.values())==11,'sphere source')
   p={m:(-2 if c==-4 else c) for m,c in p.items() if m}
  rs.append(p)
 rs.append({():s-1,(q,):1,(z,):-4,(z,z):-4})
 return compact(e,rs)
def stage(e,ops):
 rows=[poly(r['terms']) for r in e['residuals']]
 for op in ops:
  k=op['kind']
  if k=='row_add':
   i,j,a=op['i'],op['j'],op['k'];need(i!=j,'self row');rows[i]=add(rows[i],rows[j],a)
  elif k=='shear':
   i,j,a=op['i'],op['j'],op['k'];need(i!=j,'self shear');rows=[subst(p,j,{(j,):1,(i,):a}) for p in rows]
  elif k=='shear_form':
   v=op['variable'];f=poly(op['replacement']);need(f.get((v,))==1 and all(len(m)==1 for m in f),'shear form');rows=[subst(p,v,f) for p in rows]
  elif k=='project':
   i,v=op['row'],op['variable'];f=poly(op['replacement']);need(all(v not in m and len(m)<=2 for m in f),'polynomial projection');target=add({(v,):1},f,-1);need(max(map(len,f),default=0)<2 or all(v not in m or len(m)==1 for j,p in enumerate(rows) if j!=i for m in p),'quadratic variable must occur linearly elsewhere');need(rows[i]==target or rows[i]=={m:-c for m,c in target.items()},'unit defining row');rows=[subst(p,v,f) for p in rows]
  else:raise ValueError(k)
  need(all(len(m)<=2 for p in rows for m in p),'degree')
 return compact(e,rows)
def result(e):
 p={}
 for r in e['residuals']:
  q=poly(r['terms']);p=add(p,mul(q,q))
 metrics=dict(variables=len(e['variables']),rows=len(e['residuals']),degree=max(map(len,p)),monomials=len(p),height=max(map(abs,p.values())),row_height=max(abs(c) for r in e['residuals'] for c,m in r['terms']))
 return dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=len(e['variables']),terms=terms(p)),metrics

def main(check=False):
 pins=read(ROOT/'SOURCE_PINS.json')
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'source pin '+p)
 summary={}
 for name in read(ROOT/'ENDPOINTS.json'):
  cert=read(ROOT/'certificates'/f'{name}.json');e=initial()
  for ops in cert['stages']:e=stage(e,ops)
  e['variant']=name;exp,m=result(e);summary[name]=m;d=ROOT/name;d.mkdir(exist_ok=True)
  for f,x in [('equation.json',e),('expanded_polynomial.json',exp),('METRICS.json',m)]:
   if check:need((d/f).read_bytes()==raw(x),'mismatch '+str(d/f))
   else:(d/f).write_bytes(raw(x))
 print(json.dumps(summary,indent=2))
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');main(a.parse_args().check)
