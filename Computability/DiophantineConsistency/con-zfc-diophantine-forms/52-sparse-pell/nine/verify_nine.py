#!/usr/bin/env python3
"""Independent finite checks of the round-7 implementation, not a consistency proof."""
from pathlib import Path
from collections import Counter
from math import isqrt
from itertools import product
import json,random,hashlib,gzip
ROOT=Path(__file__).resolve().parent

def recipe(ts,ps,mod=None):
 result=0
 for t in ts:
  a=t['coefficient']
  for p,e in zip(ps,t['powers']):a*=pow(p,e,mod) if mod else p**e
  result+=a
 return result%mod if mod else result

def run(obj,values,ports,p):
 fixed={r['name']:recipe(r['terms'],ports,p) for r in obj['coefficient_recipes']};fixed['radix_scale']=pow(2,obj['radix_scale_exponent'],p)
 vals=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='literal':x=n['value']
  elif k=='variable':x=values[n['name']]
  elif k=='fixed':x=fixed[n['name']]
  else:
   a,b=vals[n['left']],vals[n['right']];x=a+b if k=='add' else a-b if k=='sub' else a*b
  vals.append(x%p)
 return vals[obj['output']],{k:vals[v] for k,v in obj['named_nodes'].items()}

def lead(obj):
 # Leading homogeneous coefficient, represented as a polynomial in lambda.
 def plus(a,b,sign=1):
  c=a.copy()
  for e,x in b.items():c[e]=c.get(e,0)+sign*x
  return {e:x for e,x in c.items() if x}
 def times(a,b):
  c={}
  for e,x in a.items():
   for f,y in b.items():c[e+f]=c.get(e+f,0)+x*y
  return {e:x for e,x in c.items() if x}
 fixed={r['name']:recipe(r['terms'],[2,3,5,7]) for r in obj['coefficient_recipes']};vals=[]
 for ix,n in enumerate(obj['nodes']):
  k=n['kind']
  if k=='variable':a=(1,{0:1})
  elif k=='literal':a=(0,{0:n['value']}) if n['value'] else (-1,{})
  elif k=='fixed':a=(0,{1:1}) if n['name']=='radix_scale' else (0,{0:fixed[n['name']]})
  else:
   (da,ca),(db,cb)=vals[n['left']],vals[n['right']]
   if k=='mul':a=(da+db,times(ca,cb)) if ca and cb else (-1,{})
   elif da>db:a=(da,ca)
   elif db>da:a=(db,{e:(-x if k=='sub' else x) for e,x in cb.items()})
   else:
    cc=plus(ca,cb,-1 if k=='sub' else 1)
    if not cc and da>0:raise AssertionError(('unresolved cancellation',ix,n,da))
    a=(da,cc) if cc else (-1,{})
  vals.append(a)
 return vals[obj['output']],{k:vals[v][0] for k,v in obj['named_nodes'].items()}

def finalizer(a,b,V,W,u,v,m,M,n):
 o=u*m;theta=u*n+v-o*(V+W)
 return (theta*theta-o*o*(a+b))**2-4*o**4*a*b

def main():
 if not __debug__:raise RuntimeError('Assertions required')
 rng=random.Random(809414);reports=[]
 binding=json.loads((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_text());ports=[]
 for row in binding['ports']:
  raw=(ROOT.parent/'coefficients'/row['file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==row['sha256'];x=int.from_bytes(raw,'little');assert x.bit_length()==row['bits'];ports.append(x)
 for path in sorted((ROOT/'generated').glob('nine_*_positive.json')):
  obj=json.loads(path.read_text());cert=json.loads(path.with_name(path.stem+'_degree_certificate.json').read_text());nat=json.loads(path.with_name(path.name.replace('_positive','_natural')).read_text());natc=json.loads(path.with_name(path.name.replace('_positive','_natural_degree_certificate')).read_text())
  for x in [obj,cert,nat,natc]:
   assert len(x['variables'])==9 and len(set(x['variables']))==9
   assert x['total_operations']==sum(Counter(n['kind'] for n in x['nodes'] if 'left' in n).values())
   assert x['degree']==964*x['source_degree_N']+8*x['W']+236
   target=ROOT.parent/x['target_file'];assert hashlib.sha256(target.read_bytes()).hexdigest()==x['target_sha256']
  for p in [1000000007,1000000009,2147483647]:
   for _ in range(60):
    values={x:rng.randrange(1,80) for x in obj['variables']};ps=[rng.randrange(1,1000) for _ in range(4)]
    answer,names=run(obj,values,ps,p);cert_answer,cert_names=run(cert,values,ps,p);assert cert_answer==answer
    for register in ['Dcode','Jcode','Scode','Tcode','N','R']:assert names[register]==cert_names[register]
    shifted={x:y-1 for x,y in values.items()};assert run(nat,shifted,ps,p)[0]==answer;assert run(natc,shifted,ps,p)[0]==answer
    assert names['F']==((names['D']-1)*names['L']**2+1)%p
    assert (names['Tpair']**2-64*names['D']*names['F'])%p==((8*names['D']+1)*names['k']**2-64*names['D'])%p
   for _ in range(5):
    values={x:rng.randrange(1,80) for x in obj['variables']};assert run(obj,values,ports,p)[0]==run(cert,values,ports,p)[0]
  degree,names=lead(cert);e=obj['diagonal_leading_coefficient'];assert degree==(obj['degree'],{e['radix_scale_power']:2**e['power_of_two']}),(path,degree,e)
  assert all(abs(recipe(r['terms'],ports))<(1<<obj['coefficient_bound_exponent']) for r in obj['coefficient_recipes'])
  reports.append({'file':path.name,'operations':obj['total_operations'],'degree':degree[0],'leading_coefficient':e,'named_degrees':names,'modular_replays':180,'actual_tuple_replays':15})
 # Universal finite finalizer sanity checks, including nonsquare obstructions.
 tests=0
 for a,b,u,v,m,n in product(range(1,10),range(1,10),[1,2,3],range(1,5),[-2,-1,0,1,2],range(6)):
  if a==b:continue
  V=isqrt(a)+1;W=isqrt(b)+1;M=6
  if finalizer(a,b,V,W,u,v,m,M,n)==0:
   assert m>0 and isqrt(a)**2==a and isqrt(b)**2==b and v%u==0
  tests+=1
 complete=0
 for r,s,u,m in product(range(1,8),range(1,8),range(1,5),range(1,4)):
  if r==s:continue
  V,W,M,v=r+1,s+1,6,2*u;n=m*(V+W+r+s)-v//u
  assert n>=0 and finalizer(r*r,s*s,V,W,u,v,m,M,n)==0;complete+=1
 # Exact algebraic majorants at unrestricted positive arithmetic fixtures.
 for A,C,i,J in product(range(2,9),range(1,8),range(1,6),[3,7,11]):
  D=(A*A-1)*C*C+1;k=i*J*C;L=k*D;E=L*C;F=(A*A-1)*E*E+1;T=k*(8*D*D-4*D-1)
  assert F==(D-1)*L*L+1
  assert T*T-64*D*F==(8*D+1)*k*k-64*D>0
 payloads=json.loads((ROOT/'COEFFICIENT_INSTANCE.json').read_text())
 for row in payloads['fixed_leaves']:
  raw=gzip.decompress((ROOT/row['file']).read_bytes());assert hashlib.sha256(raw).hexdigest()==row['raw_sha256']
  got=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1);wanted=(1<<row['recipe']['power_of_two']) if isinstance(row['recipe'],dict) else recipe(row['recipe'],ports)
  assert got==wanted
 result={'status':'PASS','fixed_payloads_reconstructed':len(payloads['fixed_leaves']),'variants':reports,'finalizer_soundness_fixtures':tests,'finalizer_completeness_fixtures':complete,'majorant_fixtures':7*7*5*3,'limitations':'Finite implementation checks only. Mathematical equivalence uses the stated source compiler and Jones numerical ratio theorems.'}
 (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='variants'}));print([(r['file'],r['degree'],r['operations']) for r in reports])
if __name__=='__main__':main()
