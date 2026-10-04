#!/usr/bin/env python3
"""Independent exact cache-key inventory and ordinary Z[W] weight evaluation."""
import collections,json,pathlib,sys
sys.dont_write_bytecode=True
import audit_exact as a
ROOT=pathlib.Path(__file__).resolve().parent
f=a.module('candidate_weight_audit',a.SNAP/'fusion_source.py')
ps,q=a.profiles();receipt=json.loads((a.SNAP/'fused-receipt.json').read_text())
_,groups=a.partitions(ps,receipt)
prepared=set()
for name,width in [('H',400),('B',400),('F',400),('Hlow',25),('Hhigh',375)]:
 for m in ps[name]:
  if m:prepared.add((width,m,0))
for name in a.KINDS:
 for p,m in q[name]:
  if p or m:prepared.add((400,p,m))
required=set()
req=[('H',a.HALF),('B',0),('B',a.HALF),('F',0),('F',a.HALF),('Hlow',0),('Hhigh',0),('first',0)]
for name,phase in req:
 if name=='first':continue
 width={'Hlow':25,'Hhigh':375}.get(name,400)
 for block,seq in groups[name,phase]:
  for v in block:
   if v:required.add((width,v,0))
for name in a.KINDS:
 for p,m in q[name]:
  if p or m:required.add((400,p,m))
assert required<=prepared
assert collections.Counter(k[0] for k in prepared)=={400:736,25:21,375:81}

class Polynomial:
 def __init__(self):self.n=self.M=self.A=0;self.values=[];self.leaves={'one':{0:1},'three':{0:3},'W':{1:1}}
 def val(self,x):return self.values[x] if type(x)is int else self.leaves[x]
 def gate(self,op,a,b):
  aa,bb=self.val(a),self.val(b);out=collections.defaultdict(int)
  if op=='*':
   for i,v in aa.items():
    for j,w in bb.items():out[i+j]+=v*w
   self.M+=1
  else:
   out.update(aa)
   for j,w in bb.items():out[j]+=w if op=='+' else -w
   self.A+=1
  r={k:v for k,v in out.items()if v};i=self.n;self.n+=1;self.values.append(r);return i
 def power(self,x,n):
  if n==0:return 'one'
  r=x
  for b in bin(n)[3:]:
   r=self.gate('*',r,r)
   if b=='1':r=self.gate('*',r,x)
  return r
p=Polynomial();zero=p.gate('-','one','one');fu=f.Fusion(p,'W',{'labels':{'0':zero}},None,None)
weights=[];seen=set()
# Mirror only call order to compare cache counts. Targets are direct sparse coefficients.
for name,phase in req:
 for block,seq in groups[name,phase]:
  got=fu.weight(seq);expect={600*k:1 for k in seq}
  assert p.val(got)==expect
  if seq not in seen:weights.append({'positions':list(seq),'polynomial_terms':len(expect),'min_degree':min(expect),'max_degree':max(expect)})
  seen.add(seq)
assert len(seen)==18 and len(fu.weight_cache)==18
assert p.M-12==300 and p.A-1==111 # 119 powers+168 geometric+13 run; 104 geometric+7 run.
# The actual geometric routine is independently evaluated in Z[Y] for all used n.
geometric=[]
for n in sorted(fu.geom):
 g=Polynomial();power,series=f.geometric(g,'W',n)
 assert g.val(power)=={n:1} and g.val(series)=={k:1 for k in range(n)}
 geometric.append({'length':n,'M':g.M,'A':g.A})
result={'status':'PASS_EXACT_POLYNOMIAL_WEIGHTS_AND_CACHE_CLOSURE','all_profile_gets_cached':True,'prepared_nonzero_profile_keys':len(prepared),'required_nonzero_profile_keys':len(required),'cache_by_width':dict(collections.Counter(k[0]for k in prepared)),'profile_cache_not_extended_during_fusion':True,'weight_polynomials_verified_over_ZW':len(weights),'weight_only_M':p.M-12,'weight_only_A':p.A-1,'weights':weights,'geometric_pairs':geometric,'no_modular_evaluation':True,'script_sha256':a.digest(pathlib.Path(__file__))}
a.dump(ROOT/'caches-weights-receipt.json',result)
print(result['status'])
