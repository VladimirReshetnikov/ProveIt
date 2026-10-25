#!/usr/bin/env python3
"""Reconstruct a final polynomial from its frozen finite transformation certificate."""
from pathlib import Path
from collections import defaultdict
import argparse,copy,json

def read(p):return json.loads(p.read_text())
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def poly(ts):return {tuple(m):c for c,m in ts}
def add(*ps):
 out=defaultdict(int)
 for p in ps:
  for m,c in p.items():out[m]+=c
 return {m:c for m,c in out.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def mul(p,q):
 out=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():out[tuple(sorted(m+n))]+=c*d
 return {m:c for m,c in out.items() if c}
def sub(p,x,r):
 out={}
 for m,c in p.items():
  t={():c}
  for i in m:t=mul(t,r if i==x else {(i,):1})
  out=add(out,t)
 return out
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]

def replay(srcdir,out):
 source=read(srcdir/'source.json');cert=read(srcdir/'certificate.json');pc=read(srcdir/'projection_certificate.json')
 rows=[poly(r['terms']) for r in source['residuals']];names={v['name']:i for i,v in enumerate(source['variables'])}
 for name,d in cert['coordinate_shears']:
  x=names[name];r=add({(x,):1},{(names[k],):v for k,v in d.items()});rows=[sub(p,x,r) for p in rows]
 for i,j,k in cert['exposure_operations']:rows[i]=add(rows[i],scale(rows[j],k))
 rows=dict(enumerate(rows))
 for st in pc['steps']:
  del rows[st['row_id']];x=st['variable'];r=poly(st['restoration']);rows={i:sub(p,x,r) for i,p in rows.items()}
 keep=pc['retained_original_variables'];ren={x:i for i,x in enumerate(keep)}
 rr=[{tuple(ren[x] for x in m):c for m,c in rows[i].items()} for i in sorted(rows)]
 for i,j,k in cert['final_operations']:rr[i]=add(rr[i],scale(rr[j],k))
 P=add(*[mul(p,p) for p in rr]);metrics={'variables':len(keep),'rows':len(rr),'degree':max(map(len,P)),'monomials':len(P),'height':max(map(abs,P.values())),'row_height':max(abs(c) for r in rr for c in r.values()),'row_operations':len(cert['final_operations']),'projection_count':len(pc['steps'])}
 eq=copy.deepcopy(source);eq['variant']+=':row_exposure_reduced';eq['metrics']=metrics;eq['refinement_certificate']='certificate.json'
 shear_targets={t for t,d in cert['coordinate_shears']}
 eq['variables']=[{'name':'x'+str(i),'source_name':source['variables'][old]['name'],'source_kind':source['variables'][old].get('kind'),'source_coordinate':old,'coordinate_was_sheared':source['variables'][old]['name'] in shear_targets} for i,old in enumerate(keep)]
 eq['residuals']=[dict(source['residuals'][old],terms=terms(p)) for old,p in zip(sorted(rows),rr)]
 xp={'domain':'unrestricted integers','schema':'sparse_integer_polynomial_v1','variables':len(keep),'terms':terms(P)}
 out.mkdir(parents=True,exist_ok=True)
 for name,x in [('equation.json',eq),('expanded_polynomial.json',xp),('METRICS.json',metrics)]:
  (out/name).write_bytes(canonical(x))
 print(json.dumps(metrics))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('out',type=Path);a=p.parse_args();replay(a.source,a.out)
