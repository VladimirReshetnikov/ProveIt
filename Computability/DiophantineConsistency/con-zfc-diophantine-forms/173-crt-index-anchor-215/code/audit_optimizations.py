#!/usr/bin/env python3
"""Independent coefficient-level forward/inverse audit of integer charts.

Only Python's standard library is used. No construction/optimization module
is imported. Each elementary operation has an explicit integer inverse.
"""
import argparse,json,hashlib
from pathlib import Path
from collections import defaultdict

def require(ok,why):
 if not ok:raise ValueError(why)

def plus(p,q,k=1):
 out=dict(p)
 for mon,co in q.items():
  v=out.get(mon,0)+k*co
  if v:out[mon]=v
  else:out.pop(mon,None)
 return out

def times(p,q):
 out=defaultdict(int)
 for m,a in p.items():
  for n,b in q.items():out[tuple(sorted(m+n))]+=a*b
 return {m:a for m,a in out.items() if a}

def sparse(terms,n,degree=2):
 p={}
 for item in terms:
  require(type(item) is list and len(item)==2,'term shape')
  co,mon=item
  require(type(co) is int and co!=0,'coefficient must be a nonzero integer')
  require(type(mon) is list and len(mon)<=degree and mon==sorted(mon),'invalid monomial')
  require(all(type(i) is int and 0<=i<n for i in mon),'coordinate index')
  key=tuple(mon);require(key not in p,'duplicate monomial');p[key]=co
 return p

def read_equation(path):
 raw=path.read_bytes();doc=json.loads(raw);n=len(doc['variables'])
 require(doc['domain']=='unrestricted integers','wrong domain')
 return raw,doc,[sparse(r['terms'],n) for r in doc['residuals']]

def substitute(p,i,expr):
 out={}
 for mon,co in p.items():
  term={():co}
  for j in mon:term=times(term,expr if j==i else {(j,):1})
  out=plus(out,term)
 return out

def apply(rows,ops,n,inverse=False):
 rows=[dict(r) for r in rows]
 for op in (reversed(ops) if inverse else ops):
  if op['type']=='row':
   i,j,k=op['target'],op['source'],op['multiple']
   require(type(i) is int and type(j) is int and 0<=i<len(rows) and 0<=j<len(rows) and i!=j,'noninvertible row operation')
   require(type(k) is int,'row multiplier')
   rows[i]=plus(rows[i],rows[j],-k if inverse else k)
  else:
   i=op['coordinate'];require(type(i) is int and 0<=i<n,'shear coordinate')
   im=sparse(op['image'],n,degree=1)
   require(im.get((i,))==1,'shear must have own coefficient one')
   if inverse:im=plus({(i,):2},im,-1)
   rows=[substitute(r,i,im) for r in rows]
 return rows

def get_ops(kind,cert,n):
 if kind=='chart':
  return [{'type':'coordinate','coordinate':o['coordinate'],'image':[[1,[o['coordinate']]],[-1,[o['subtract_coordinate']]]]} for o in cert['operations']]
 if kind=='basis':
  return [{'type':'row','target':i,'source':j,'multiple':k} for i,j,k in cert]
 if kind=='translations':
  return [{'type':'coordinate','coordinate':i,'image':[[1,[i]],[k,[]]]} for i,k in cert['operations']]
 if kind=='shear':return cert['operations']
 raise ValueError('unknown operation kind')

def collect(rows):
 q={}
 for r in rows:q=plus(q,times(r,r))
 return q

def metrics(doc,rows):
 poly=collect(rows);n=len(doc['variables'])
 require({i for mon in poly for i in mon}==set(range(n)),'unused polynomial coordinate')
 return {'variables':n,'rows':len(rows),'degree':max(map(len,poly)),
   'monomials':len(poly),'height':max(map(abs,poly.values())),
   'row_height':max(abs(c) for r in rows for c in r.values())},poly

def main(manifest_path,receipt_path):
 manifest_path=manifest_path.resolve();base=manifest_path.parent
 manifest=json.loads(manifest_path.read_bytes());receipt={'ok':True,'profiles':[]}
 for prof in manifest['profiles']:
  source=base/prof['source'];raw,doc,rows=read_equation(source)
  original_rows=[dict(r) for r in rows];whole=[];n=len(doc['variables']);steps=[]
  for stage in prof['stages']:
   require(hashlib.sha256(raw).hexdigest()==stage['input_sha256'],'stage source hash')
   cert=json.loads((base/stage['certificate']).read_bytes());ops=get_ops(stage['kind'],cert,n)
   if type(cert) is dict:
    pin=cert.get('parent_sha256',cert.get('parent_hash'))
    if pin is not None:require(pin==hashlib.sha256(raw).hexdigest(),'certificate source hash')
   out_raw,out_doc,out_rows=read_equation(base/stage['equation'])
   require(len(out_doc['variables'])==n,'coordinate count changed')
   require(hashlib.sha256(out_raw).hexdigest()==stage['output_sha256'],'stage target hash')
   require(apply(rows,ops,n)==out_rows,'forward residual identity mismatch')
   require(apply(out_rows,ops,n,inverse=True)==rows,'inverse residual identity mismatch')
   measure,collected=metrics(out_doc,out_rows)
   expanded=base/stage['equation'];expanded=expanded.parent/'expanded_polynomial.json'
   if expanded.exists():
    e=json.loads(expanded.read_bytes())
    require(e['variables']==n,'expansion variable count')
    require(sparse(e['terms'],n,degree=4)==collected,'expanded coefficient mismatch')
   steps.append({'kind':stage['kind'],'operations':len(ops),'sha256':stage['output_sha256'],'metrics':measure})
   rows,raw,doc=out_rows,out_raw,out_doc;whole+=ops
  require(apply(rows,whole,n,inverse=True)==original_rows,'composed inverse mismatch')
  measure,_=metrics(doc,rows)
  receipt['profiles'].append({'name':prof['name'],'metrics':measure,'steps':steps,'total_elementary_operations':len(whole),'composed_inverse_checked':True,'equation_sha256':hashlib.sha256(raw).hexdigest()})
 print(json.dumps(receipt,indent=2))
 receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('manifest',type=Path);p.add_argument('--receipt',type=Path,default=Path('OPTIMIZATION_AUDIT.json'));a=p.parse_args();main(a.manifest,a.receipt)
