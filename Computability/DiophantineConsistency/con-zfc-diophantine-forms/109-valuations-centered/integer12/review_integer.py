from pathlib import Path
import json,hashlib,gzip,collections,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parent
def req(x,m):
 if not x:raise ValueError(m)
packets=[]
for p in sorted((R/'equations').glob('*.json')):
 d=json.loads(p.read_text());nodes=d['nodes'];seen=set();cnt=collections.Counter();deg=[]
 for i,n in enumerate(nodes):
  if n[0] in ['add','sub','mul']:
   req(0<=n[1]<i and 0<=n[2]<i,'topology');cnt[n[0]]+=1;deg.append(deg[n[1]]+deg[n[2]] if n[0]=='mul' else max(deg[n[1]],deg[n[2]]))
  else:deg.append(1 if n[0]=='variable' else 0)
 def visit(i):
  if i in seen:return
  seen.add(i);n=nodes[i]
  if n[0] in ['add','sub','mul']:visit(n[1]);visit(n[2])
 visit(d['output']);req(len(seen)==len(nodes),'liveness');req(sum(cnt.values())==d['operations'],'count')
 req(set(n[1] for n in nodes if n[0]=='variable')==set(d['variables']),'variables')
 packets.append({'name':p.name,'operations':sum(cnt.values()),'claimed_degree':d['exact_degree'],'syntactic_degree':deg[d['output']],'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
binding=json.loads((R/'coefficients/BINDING.json').read_text());coeff={}
for key,v in binding['payloads'].items():
 b=gzip.decompress((R/'coefficients'/v['file']).read_bytes());req(hashlib.sha256(b).hexdigest()==v['raw_sha256'],'coefficient hash')
 coeff[key]=int.from_bytes(b,'little')
req(coeff['beta']%3==1,'beta residue')
# Exact symbolic quadratic-algebra identity for the new pure19 carrier.
class Poly(dict):
 def __add__(self,o):
  if not isinstance(o,Poly):o=Poly({(0,0,0,0):o})
  q=Poly(self)
  for k,v in o.items():q[k]=q.get(k,0)+v
  return Poly({k:v for k,v in q.items() if v})
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.items()})
 def __sub__(self,o):return self+-as_poly(o)
 def __rsub__(self,o):return as_poly(o)+-self
 def __mul__(self,o):
  o=as_poly(o);q=Poly()
  for a,x in self.items():
   for b,y in o.items():
    k=tuple(i+j for i,j in zip(a,b));q[k]=q.get(k,0)+x*y
  return Poly({k:v for k,v in q.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  q=as_poly(1)
  for _ in range(n):q=q*self
  return q
 def reduced(self):
  q=Poly()
  for (a,b,c,d),v in self.items():
   k=(a,b,c+d//2,d%2);q[k]=q.get(k,0)+v
  return Poly({k:v for k,v in q.items() if v})
def as_poly(v):return v if isinstance(v,Poly) else Poly({(0,0,0,0):v})
u,H,D,d=[Poly({tuple(int(i==j) for i in range(4)):1}) for j in range(4)]
Q0=u*u+D+3*H*H;C0=u*(u*u+3*D)-19*H**3;C1=3*u*u+D
A=Q0*C0+2*u*D*C1;B=Q0*C1+2*u*C0
rem=(((u+d)**2+3*H**2)*((u+d)**3-19*H**3)-(A+B*d)).reduced()
req(not rem,'carrier identity')
req(sum(v for (up,hp,dp,rp),v in B.items() if hp==0 and rp==0)%3==1,'B unit')
# Finite prime-power behavior supplements the Hensel/CRT proof.
pi=lambda x:(x*x+3)*(x*x*x-19)
for m in range(1,513):req(any(pi(x)%m==0 for x in range(m)),f'intersectivity slice {m}')
g=lambda x:3*x**3+3*x*x+x-2
x=2;mod=3
for k in range(2,21):
 x=next(x+t*mod for t in range(3) if g(x+t*mod)%(3*mod)==0);mod*=3
 req(((1+3*x)**3-19)%(9*mod)==0,'3-adic lift')
result={'review_scope':'New integer prime-three separator, carrier, scale, and exact-degree proof; inherited generalized signed-kernel calibration retained as dependency.','literal_packets':packets,'six_coefficients_authenticated':True,'pure19_quadratic_algebra_identity':True,'intersectivity_finite_moduli':[1,512],'three_adic_lift_exponent':22,'limitations':'Finite checks supplement ordinary proofs, not an internal ZFC certificate.'}
(R/'REVIEW_FRONTIER_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
