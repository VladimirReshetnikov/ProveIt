#!/usr/bin/env python3
"""Independent exact refinement verifier; no producing modules are imported."""
from pathlib import Path
import argparse,collections,copy,hashlib,json

def need(c,m):
 if not c:raise ValueError(m)
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def read(p):return json.loads(p.read_text())
def poly(ts):
 d=collections.defaultdict(int)
 for c,m in ts:
  need(type(c) is int and all(type(i) is int and i>=0 for i in m),'integer term')
  d[tuple(sorted(m))]+=c
 return {m:c for m,c in d.items() if c}
def plus(*args):
 d=collections.defaultdict(int)
 for p in args:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def times(p,q):
 d=collections.defaultdict(int)
 for m,c in p.items():
  for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items() if c}
def sub(p,v,repl):
 out={}
 for m,c in p.items():
  q={():c}
  for x in m:q=times(q,repl if x==v else {(x,):1})
  out=plus(out,q)
 return out
def unit(x):return {(x,):1}
def degree(p):return max(map(len,p),default=0)
def apply_ops(rows,ops):
 for i,j,k in ops:
  need(type(i) is int and type(j) is int and type(k) is int,'integer row operation')
  need(i!=j and 0<=i<len(rows) and 0<=j<len(rows),'row index')
  old=rows[i];rows[i]=plus(old,scale(rows[j],k))
  need(plus(rows[i],scale(rows[j],-k))==old,'row inverse')
 return rows

def verify(root):
 src=read(root/'source.json');cert=read(root/'certificate.json');ex=read(root/'exposed.json');pc=read(root/'projection_certificate.json');pr=read(root/'projected.json');eq=read(root/'equation.json');xp=read(root/'expanded_polynomial.json')
 need(src['domain']=='unrestricted integers' and eq['domain']=='unrestricted integers','domain')
 need(hashlib.sha256(canonical(src)).hexdigest()==cert['source_sha256'],'source hash')
 names={v['name']:i for i,v in enumerate(src['variables'])};need(len(names)==len(src['variables']),'unique names')
 rows=[poly(r['terms']) for r in src['residuals']]
 for target,inputs in cert['coordinate_shears']:
  x=names[target];need(target not in inputs and all(type(c) is int for c in inputs.values()),'coordinate shear')
  L={(names[k],):c for k,c in inputs.items() if c};p=plus(unit(x),L)
  need(sub(p,x,plus(unit(x),scale(L,-1)))==unit(x),'coordinate inverse')
  rows=[sub(r,x,p) for r in rows]
 apply_ops(rows,cert['exposure_operations'])
 need([poly(r['terms']) for r in ex['residuals']]==rows and ex['variables']==src['variables'],'exposed graph')
 need(hashlib.sha256(canonical(ex)).hexdigest()==pc['input_sha256'],'projection input hash')
 need(hashlib.sha256(canonical(pr)).hexdigest()==pc['output_sha256'],'projection output hash')
 rr=dict(enumerate(rows));deleted=set()
 for st in pc['steps']:
  row,x=st['row_id'],st['variable'];r=poly(st['restoration'])
  need(row in rr and x not in deleted and all(x not in m for m in r),'monic step target')
  p=plus(unit(x),scale(r,-1));need(rr[row] in (p,scale(p,-1)),'literal monic restoration')
  need(degree(r)<=2,'restoration degree')
  del rr[row];deleted.add(x)
  rr={i:sub(p,x,r) for i,p in rr.items()}
  need(all(degree(p)<=2 for p in rr.values()),'quadratic degree after projection')
 keep=pc['retained_original_variables'];unused=pc['unconstrained_removed'];n=len(src['variables'])
 need(len(keep)==len(set(keep)) and len(unused)==len(set(unused)),'unique coordinate partition')
 need(set(keep).isdisjoint(deleted) and set(unused).isdisjoint(deleted|set(keep)),'disjoint coordinate partition')
 need(set(keep)|set(unused)|deleted==set(range(n)),'complete coordinate partition')
 need(all(x not in m for p in rr.values() for m in p for x in unused),'unconstrained coordinate absent')
 need(sorted(rr)==pc['retained_original_rows'],'row partition')
 ren={x:i for i,x in enumerate(keep)}
 reduced=[{tuple(ren[x] for x in m):c for m,c in rr[i].items()} for i in sorted(rr)]
 need(pr['variables']==[src['variables'][i] for i in keep],'projected names')
 need(reduced==[poly(r['terms']) for r in pr['residuals']],'all projected rows')
 apply_ops(reduced,cert['final_operations'])
 need(reduced==[poly(r['terms']) for r in eq['residuals']],'all final rows')
 targets={t for t,d in cert['coordinate_shears']}
 expected_variables=[{'name':'x'+str(i),'source_name':v['name'],'source_kind':v.get('kind'),'source_coordinate':keep[i],'coordinate_was_sheared':v['name'] in targets} for i,v in enumerate(pr['variables'])]
 need(eq['variables']==expected_variables,'literal coordinate names and provenance')
 need(all(degree(p)<=2 for p in reduced),'quadratic residuals')
 P=plus(*[times(p,p) for p in reduced]);need(P==poly(xp['terms']),'all SOS coefficients')
 used={x for m in P for x in m};need(used==set(range(len(keep))),'all coordinates live')
 metrics={'variables':len(keep),'rows':len(reduced),'degree':degree(P),'monomials':len(P),'height':max(map(abs,P.values())),'row_height':max(abs(c) for p in reduced for c in p.values()),'row_operations':len(cert['final_operations']),'projection_count':len(pc['steps'])}
 need(metrics==read(root/'METRICS.json')==eq['metrics'],'all metrics including embedded metadata')
 return {'status':'PASS','metrics':metrics,'coordinate_bijections':len(cert['coordinate_shears']),'exposure_row_operations':len(cert['exposure_operations']),'monic_inverse_steps':len(pc['steps']),'final_reversible_row_operations':len(cert['final_operations']),'complete_collected_coefficients':len(P),'imports_producer':False}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('endpoints',type=Path,nargs='+');a=p.parse_args();print(json.dumps({str(d):verify(d) for d in a.endpoints},indent=2))
