#!/usr/bin/env python3
"""Independent standard-library exact polynomial checker and coefficient audit.
No builder module or upstream executable is imported.
"""
from pathlib import Path
from collections import defaultdict
from math import factorial
import ast,gzip,hashlib,json
ROOT=Path(__file__).resolve().parent
SHIFT={'F','alpha','z','h','i','j','s','w','eta','zeta','gamma','g'}
HASH='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'

def need(v,msg):
 if not v:raise ValueError(msg)
def add(p,q,sign=1):
 r=dict(p)
 for m,c in q.items():r[m]=r.get(m,0)+sign*c
 return {m:c for m,c in r.items() if c}
def mul(p,q):
 r=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():r[tuple(a+b for a,b in zip(m,n))]+=c*d
 return {m:c for m,c in r.items() if c}
def expr(text,env,d):
 def ev(n):
  if isinstance(n,ast.Constant) and type(n.value)is int:return {(0,)*d:n.value} if n.value else {}
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {m:-c for m,c in ev(n.operand).items()}
  if isinstance(n,ast.BinOp):
   p=ev(n.left)
   if isinstance(n.op,ast.Pow):
    need(isinstance(n.right,ast.Constant) and type(n.right.value)is int and 0<=n.right.value<=8,'Unsafe power')
    r={(0,)*d:1}
    for _ in range(n.right.value):r=mul(r,p)
    return r
   q=ev(n.right)
   if isinstance(n.op,ast.Add):return add(p,q)
   if isinstance(n.op,ast.Sub):return add(p,q,-1)
   if isinstance(n.op,ast.Mult):return mul(p,q)
  raise ValueError(ast.dump(n))
 return ev(ast.parse(text,mode='eval').body)
def main():
 data=(ROOT/'data/source_system60.json').read_bytes();need(hashlib.sha256(data).hexdigest()==HASH,'Source hash')
 raw=json.loads(data);out=json.loads((ROOT/'selective12_source.json').read_text());n=31;d=35;z=(0,)*d
 unit=lambda i:tuple(int(i==j)for j in range(d))
 env={name:({unit(i):1,z:1} if name in SHIFT else {unit(i):1})for i,name in enumerate(raw['variables']+raw['constants'])}
 get=lambda x:({z:x}if x else {})if type(x)is int else env[x]
 for name,op,a,b in raw['source']:env[name]=mul(get(a),get(b))if op=='*'else add(get(a),get(b),1 if op=='+'else -1)
 rows=[add(get(a),get(b),-1)for a,b in raw['comparisons']]
 need(len(rows)==22,'Row count');need(set(out['shifted_coordinates'])==SHIFT,'Shift set')
 ports={p:{tuple(int(i==j)for j in range(4)):1}for i,p in enumerate(raw['constants'])}
 active=set();records=[]
 for j,(p,row)in enumerate(zip(rows,out['rows']),1):
  rebuilt={}
  for term in row['terms']:
   a=tuple(term['alpha']);need(sum(a)<=2,'Quadratic term');active.add(a)
   c=expr(term['coefficient'],ports,4);wc=expr(term['weighted_coefficient'],ports,4)
   weight=factorial(2-sum(a))
   for t in a:weight*=factorial(t)
   need(wc=={m:weight*v for m,v in c.items()},'Factorial weighting')
   rebuilt=add(rebuilt,{a+m:v for m,v in c.items()})
   records.append((j,a,wc))
  need(rebuilt==p,f'Exact row {j}')
 need(len(records)==109 and len(active)==62,'Support counts')
 need(rows[1].get(z)==-1,'Nonzero natural origin')
 names=raw['constants'];binding=json.loads((ROOT.parent/'native/COEFFICIENT_BINDING.json').read_text())
 vals={};payload=[]
 for name in names:
  path=ROOT.parent/'native'/binding['binding'][name];b=gzip.decompress(path.read_bytes());val=int.from_bytes(b,'little');vals[name]=val
  matching=next(x for x in binding['ports']if x['name']=={'K0':'K','MF':'MF_source'}.get(name,name))
  need(hashlib.sha256(b).hexdigest()==matching['sha256'],'Port hash')
  payload.append(dict(name=name,bits=val.bit_length(),sha256=matching['sha256']))
 need(vals['beta']>0 and vals['K0']>0,'Positivity assumptions')
 maximum=0;mass=1;triangle=0;zeros=0
 for j,a,recipe in records:
  v=0;bound=0
  for powers,c in recipe.items():
   t=1
   for name,pow in zip(names,powers):t*=vals[name]**pow
   v+=c*t;bound+=abs(c)*(1<<sum(pow*vals[name].bit_length()for name,pow in zip(names,powers)))
  need(abs(v)<=bound,'Triangle coefficient bound')
  maximum=max(maximum,abs(v));mass+=abs(v);triangle=max(triangle,bound);zeros+=not bool(v)
 strict_exp=maximum.bit_length();need(maximum<1<<strict_exp,'Strict coefficient bound')
 kappa=strict_exp+13
 if kappa%2:kappa+=1
 need((1<<kappa)>=8192*(1<<strict_exp),'Sparse source bound')
 report=dict(status='PASS',method='Independent exact sparse polynomial expansion over 35 symbols; standard library only',source_sha256=HASH,shifted_coordinates=sorted(SHIFT),source_rows=22,coefficient_records=109,active_monomials=62,quadratic_active=39,linear_active=22,origin_row2=-1,ports=payload,zero_specialized_coefficients=zeros,maximum_actual_weighted_coefficient_bits=strict_exp,total_weighted_coefficient_mass_bits=mass.bit_length(),triangle_bound_bits=triangle.bit_length(),strict_M_definition=f'2^{strict_exp}',sparse_source_kappa=kappa,sparse_source_bound='2^kappa >= 8192 M > 8192 times every absolute weighted coefficient',scope='Finite affine identities, support, source-origin guard and explicit native coefficient bounds; positivity equivalence is the separate elementary proof, and compiler/calibration remain inherited.')
 (ROOT/'SELECTIVE_SOURCE_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
