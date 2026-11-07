#!/usr/bin/env python3
"""Independent structural, degree and finite-control checks for sign25."""
import hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;h=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest();old=p.parent/'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';new=p/'seed.json'
if h(old)!='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25' or h(new)!='c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8':raise SystemExit('seed pin')
a,b=json.loads(old.read_text()),json.loads(new.read_text());ar=a['residuals'];br=b['residuals']
assert len(ar)==17 and len(br)==16 and b['total_coordinates']==26 and b['witness_count']==25 and b['coefficient_binding']==a['coefficient_binding']
def match(x,y):
 if x[0]=='var':
  i=x[1]
  return y==(['mul',['var',17],['var',18]] if i==19 else ['var',i if i<19 else i-1])
 if x[0] in ('num','port'):return x==y
 return x[0] in ('add','sub','mul') and len(x)==len(y)==3 and x[0]==y[0] and match(x[1],y[1]) and match(x[2],y[2])
assert [r['gate'] for r in br]==[r['gate'] for r in ar if r['gate']!='ell']
assert next(r['expr'] for r in ar if r['gate']=='ell')==['sub',['var',19],['mul',['var',17],['var',18]]]
for x,y in zip((r for r in ar if r['gate']!='ell'),br):assert x['kind']==y['kind'] and match(x['expr'],y['expr'])
def degree(t,weighted=False):
 if t[0]=='var':return int(t[1] in (17,18)) if weighted else 1
 if t[0] in ('num','port'):return 0
 assert t[0] in ('add','sub','mul') and len(t)==3
 a,b=degree(t[1],weighted),degree(t[2],weighted)
 return a+b if t[0]=='mul' else max(a,b)
degrees={r['gate']:degree(r['expr']) for r in br};weighted={r['gate']:degree(r['expr'],True) for r in br};assert max(degrees.values())==4 and weighted['N0']==4 and all(d<=2 for n,d in weighted.items() if n!='N0')
def ports(t):
 if t[0]=='port':return {t[1]}
 if t[0] in ('num','var'):return set()
 return ports(t[1])|ports(t[2])
n0=next(r['expr'] for r in br if r['gate']=='N0');assert not ports(n0)
def poly(t):
 op=t[0]
 if op=='num':return [t[1]]
 if op=='port':return [0]
 if op=='var':return [0,1] if t[1] in (17,18) else [0]
 x,y=poly(t[1]),poly(t[2])
 if op=='mul':
  z=[0]*(len(x)+len(y)-1)
  for i,a in enumerate(x):
   for j,b in enumerate(y):z[i+j]+=a*b
 else:
  z=[0]*max(len(x),len(y))
  for i,a in enumerate(x):z[i]+=a
  for i,b in enumerate(y):z[i]+=b if op=='add' else -b
 while len(z)>1 and z[-1]==0:z.pop()
 return z
assert poly(n0)==[-1,0,-2,0,-1]
# Audit the actual compressed coefficient files under the unchanged relative binding.
coeff=p/b['coefficient_binding']['path'];files={}
for name,rec in b['coefficient_binding']['ports'].items():
 path=coeff/rec['file'];assert h(path)==rec['gzip_sha256'];files[name]=h(path)
def value(t,v,ps):
 op=t[0]
 if op=='num':return t[1]
 if op=='var':return v[t[1]]
 if op=='port':return ps[t[1]]
 x,y=value(t[1],v,ps),value(t[2],v,ps)
 return x+y if op=='add' else x-y if op=='sub' else x*y
rng=random.Random(26025)
for _ in range(16):
 v=[rng.randrange(4) for _ in range(26)];ps={k:rng.randrange(1,5) for k in b['fixed_ports']};lift=v[:19]+[v[17]*v[18]]+v[19:];assert len(lift)==27 and lift[0]==v[0] and all(x>=0 for x in lift)
 assert value(next(r['expr'] for r in ar if r['gate']=='ell'),lift,ps)==0
 assert [value(r['expr'],lift,ps) for r in ar if r['gate']!='ell']==[value(r['expr'],v,ps) for r in br]
print(json.dumps({'status':'PASS','source_sha256':h(old),'candidate_sha256':h(new),'residual_count':len(br),'structural_transfers':len(br),'residual_syntactic_degrees':degrees,'weighted_degrees_v17_v18':weighted,'N0_univariate_coefficients_low_to_high':poly(n0),'coefficient_gzip_sha256':files,'finite_lift_controls':16,'scope':'External AST/degree and finite controls only; Lean zero-set bridge and iPRA endpoint unproved.'},indent=2,sort_keys=True))
