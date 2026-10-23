#!/usr/bin/env python3
"""New independent data verifier for simultaneous quadratic Sun10 coding."""
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter,defaultdict
import json,gzip,math,random,hashlib
R=Path(__file__).resolve().parent
C=json.loads((R/'generated/multitarget_sun10.json').read_text());records=json.loads((R/'generated/quadratic_coefficients.json').read_text())['records']
w=C['weights'];sums=[sum(t) for t in combinations_with_replacement([0]+w,2)]
assert len(sums)==528 and len(set(sums))==528 and max(w)==799
assert C['targets']==[1599*j for j in range(1,23)]
assert C['row_order']==[1,2,3,4]+list(range(6,23))+[5]
# Reconstruct row coefficients directly from original sparse residuals.
import sympy as sp
parent=json.loads((R/'data/parent_system60.json').read_text());truth={}
coordinates=sp.symbols(' '.join(parent['variables']+parent['constants']))
env={n:x+(1 if i<31 else 0) for i,(n,x) in enumerate(zip(parent['variables']+parent['constants'],coordinates))}
def get(x):return sp.Integer(x) if isinstance(x,int) else env[x]
for name,op,a,b in parent['source']:
 env[name]=get(a)*get(b) if op=='*' else get(a)+get(b) if op=='+' else get(a)-get(b)
for row,(a,b) in enumerate(parent['comparisons'],1):
 for powers,v in sp.Poly(get(a)-get(b),*coordinates).terms():
  alpha=powers[:31];factor=math.factorial(2-sum(alpha))
  for e in alpha:factor*=math.factorial(e)
  truth.setdefault((row,alpha),{})[powers[31:]]=int(v)*factor
assert len(truth)==len(records)==136
for r in records:
 assert truth[r['row'],tuple(r['alpha'])]=={tuple(t['powers']):t['coefficient'] for t in r['coefficient_polynomial_in_fixed_ports']}
 assert r['target']==C['targets'][C['row_order'].index(r['row'])]
 assert r['exponent']==r['target']-sum(a*b for a,b in zip(r['alpha'],w))
# Every target receives its own row monomial and no other row monomial.
cross=0
for r in records:
 for target in C['targets']:
  hits=sum(r['exponent']+s==target for s in sums)
  assert hits==int(target==r['target']);cross+=1
assert truth[(5,(0,)*31)]=={(0,0,0,0):2}
ports=[];payloads={}
for name,f in [('beta','beta.bin.gz'),('K0','K.bin.gz'),('MC','MC.bin.gz'),('MF','MF_source.bin.gz')]:
 raw=gzip.decompress((R/'upstream/signed10/data'/f).read_bytes());ports.append(int.from_bytes(raw,'little'));payloads[name]=hashlib.sha256(raw).hexdigest()
def coeff(row,p=None):
 ans=0
 for term in row['coefficient_polynomial_in_fixed_ports']:
  val=term['coefficient']
  for x,e in zip(ports,term['powers']):val*=pow(x,e,p) if p else x**e
  ans+=val
 return ans%p if p else ans
actual=[coeff(r) for r in records];assert max(abs(x) for x in actual)<2**2134926
# No opaque fixed leaves: every nonliteral coefficient has a recipe.
fixed={r['name']:v for r,v in zip(records,actual) if r['name'] is not None}
assert set(n['name'] for n in C['nodes'] if n['kind']=='fixed')==set(fixed)|{'beta_sun'}
def evaluate(p,point=None,degree=False):
 vals=[];degs=[];ff={k:v%p for k,v in fixed.items()};ff['beta_sun']=pow(2,C['beta_sun_exponent'],p)
 for n in C['nodes']:
  k=n['kind']
  if k=='variable':value=1 if degree else point[n['name']];d=1
  elif k=='literal':value=n['value']%p;d=0
  elif k=='fixed':value=ff[n['name']];d=0
  else:
   a,b=n['left'],n['right'];x,y=vals[a],vals[b];d=degs[a]+degs[b] if k=='mul' else max(degs[a],degs[b])
   if degree and k!='mul':x=x if degs[a]==d else 0;y=y if degs[b]==d else 0
   value=(x*y if k=='mul' else x+y if k=='add' else x-y)%p
  vals.append(value);degs.append(d)
 return vals,degs
leaders=[]
for p in [101,1009,1000003]:
 vs,ds=evaluate(p,degree=True);leaders.append({'prime':p,'degree':ds[C['output']],'coefficient':vs[C['output']]})
assert all(x['degree']==C['degree_upper_bound'] for x in leaders)
assert any(x['coefficient'] for x in leaders)
counts=Counter(n['kind'] for n in C['nodes'] if 'left'in n);assert dict(counts)==C['operation_counts'] and sum(counts.values())==C['total_operations']
# Source checks independent of the builder's sparse Horner ordering.
rng=random.Random(799);trials=0
for p in [101,1009,1000003]:
 for _ in range(40):
  point={n:rng.randrange(p) for n in C['variables']};vs,_=evaluate(p,point)
  f,g=point['f'],point['g'];b=(1+3*f)%p;B=pow(2,C['beta_sun_exponent'],p)*b*b%p
  D=sum(a*pow(B,r['exponent'],p) for r,a in zip(records,actual))%p
  ell=sum(pow(B,x,p) for x in w)%p;N0=pow(B,C['W']+1,p);N1=4*pow(B,C['Kcode']+1,p)%p;N=N0*N1%p
  power,total,block,bs,n=1,0,B,1,C['Kcode']+1
  while n:
   if n&1:total=(total+power*bs)%p;power=power*block%p
   bs=bs*(1+block)%p;block=block*block%p;n//=2
  mask=(N0-1-(b-1)*ell)%p;T=(mask+(B-2)*sum(pow(B,h,p) for h in C['targets'])*N0)%p
  J=(2*(1+g)**2*D+B*total)%p;S=(g+J*N0)%p;RR=((S+T+1)*N+T+1)%p
  expected={'b':b,'base':B,'Dcode':D,'ell':ell,'N0':N0,'N1':N1,'N':N,'Mcode':mask,'Tcode':T,'Jcode':J,'Scode':S,'Rcode':RR,'X':(N-1)*RR%p,'Y':N*N%p,'Ccap':b*pow(B,C['W'],p)%p}
  assert all(vs[C['named_nodes'][k]]==v%p for k,v in expected.items());trials+=1
# Old tail replay under four substitutions; no old code is imported/executed.
old=json.loads((R/'upstream/signed10/generated/signed10.json').read_text());tail_trials=0
for p in [101,1009,1000003]:
 for _ in range(40):
  point={n:rng.randrange(p) for n in C['variables']};vs,_=evaluate(p,point)
  replacements={old['named_nodes'][k]:vs[C['named_nodes'][k]] for k in ['b','X','Y','Ccap']};memo={}
  def ev(i):
   if i in replacements:return replacements[i]
   if i in memo:return memo[i]
   n=old['nodes'][i];k=n['kind']
   if k=='literal':r=n['value']%p
   elif k=='variable':r=point[n['name']]
   else:
    assert k in ('add','sub','mul');a,b=ev(n['left']),ev(n['right']);r=(a*b if k=='mul' else a+b if k=='add' else a-b)%p
   memo[i]=r;return r
  assert ev(old['output'])==vs[C['output']];tail_trials+=1
# Verify all final fixed leaves against their materialized signed payloads.
manifest=json.loads((R/'MULTITARGET_INSTANCE.json').read_text())
fullfixed=dict(fixed);fullfixed['beta_sun']=1<<C['beta_sun_exponent']
assert set(fullfixed)==set(manifest['fixed_leaves'])
for name,value in fullfixed.items():
 item=manifest['fixed_leaves'][name];blob=(R/item['path']).read_bytes();raw=gzip.decompress(blob)
 assert hashlib.sha256(blob).hexdigest()==item['gzip_sha256']
 assert hashlib.sha256(raw).hexdigest()==item['raw_sha256']
 assert raw[0] in (0,1)
 decoded=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1)
 assert decoded==value
assert manifest['parent_raw_sha256']==hashlib.sha256((R/'data/parent_system60.json').read_bytes()).hexdigest()
report={'all_checks_pass':True,'B2_pair_count':528,'quadratic_records_reconstructed':136,'cross_target_record_checks':cross,'max_actual_coefficient_bits':max(abs(x).bit_length() for x in actual),'source_modular_trials':trials,'tail_modular_trials':tail_trials,'exact_degree':C['degree_upper_bound'],'leading_certificates':leaders,'operations':C['total_operations'],'materialized_fixed_leaves':len(fullfixed),'fixed_port_sha256':payloads,'scope':'Exact finite identities and arithmetic transcription, not a kernel proof or a test of consistency.'}
(R/'generated/MULTITARGET_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
