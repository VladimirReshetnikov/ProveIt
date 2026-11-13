from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path('research/ordinary13-eta-zeta84-unshift-s-full-zero');parent_path=Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json');raw=parent_path.read_bytes();assert sha256(raw).hexdigest()=='ce50ab07246ad3fb77ad787fa5703fd64a8dfd94a346308b73f891225cb36f03'
g=json.loads(raw);assert len(g['source'])==85
rows=[];deleted=0
for row in g['source']:
 if row==['s','+','n_s',1]:deleted+=1;continue
 rows.append(['n_s' if x=='s' else x for x in row])
assert deleted==1 and len(rows)==84
candidate={'name':'eta/zeta-natural probe with s shift removed; full-zero obstruction, no endpoint', 'domain':g['domain'],'witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],'source':rows,'output':g['output'],'parent_sha256':sha256(raw).hexdigest()}
encoded=(json.dumps(candidate,indent=2,ensure_ascii=False)+'\n').encode()
if '--write' in sys.argv:(P/'probe.json').write_bytes(encoded)
else:assert (P/'probe.json').read_bytes()==encoded
# Exact multivariate integer polynomials in (beta,w,h,MC,MF).
N=5;zero=(0,)*N
class Poly:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,other):
  other=aspoly(other);out=self.d.copy()
  for k,v in other.d.items():out[k]=out.get(k,0)+v
  return Poly(out)
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,other):return self+-aspoly(other)
 def __rsub__(self,other):return aspoly(other)+-self
 def __mul__(self,other):
  other=aspoly(other);out={}
  for k,v in self.d.items():
   for j,w0 in other.d.items():
    key=tuple(a+b for a,b in zip(k,j));out[key]=out.get(key,0)+v*w0
  return Poly(out)
 __rmul__=__mul__
 def __eq__(self,other):return self.d==aspoly(other).d
def aspoly(x):return x if isinstance(x,Poly) else Poly({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return Poly({tuple(e):1})
beta,w,hvar,MC,MF=(var(i) for i in range(N));K0=beta*hvar-w-1;q=beta+1
R=(1+beta*beta)*(q*q-1)+MC+q*MF;k=R+1;t=(beta-1)*(w+hvar)-1;B=beta*t;rw=k*(B-1)+t+1
witness=[1,0,0,2,2,R-1,w,0,rw,1,R,1,0];ports=[beta,K0,MC,MF]
def evaluate(graph,ws,ps):
 d=dict(zip(graph['witnesses'],ws));d.update(zip(graph['fixed_numerals'],ps))
 for name,op,x,y in graph['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
v=evaluate(candidate,witness,ports)
for name,val in [('qm',beta),('q',q),('Y',0),('U',0),('E',0),('ell',0),('c',1),('R',R),('kbase',k),('Bt',B),('Z',beta),('Dstar',0),('Q',9),('I',3),('V',-1),('A0',0),('A1',0),('g72',0),('Fa',1),('out',0)]:assert v[name]==val,name
# One exact toy control, including parent at the same tuple.
toy_w=[1,0,0,2,2,43,1,0,47,1,44,1,0];toy_p=[2,0,1,1]
a=evaluate(candidate,toy_w,toy_p);b=evaluate(g,toy_w,toy_p)
assert a['out']==0 and b['out']!=0
beta_src=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();port_src=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in port_src
print(json.dumps({'parent_sha256':sha256(raw).hexdigest(),'probe_sha256':sha256(encoded).hexdigest(),'probe_rows':len(rows),'symbolic_ring_variables':['beta','w','h','MC','MF'],'symbolic_all_84_rows_evaluated':True,'symbolic_four_factor_residuals_and_output_zero':True,'natural_family_hypotheses':'beta>=2; K0,MC,MF>=0; h=ceil((K0+2)/beta); w=beta*h-K0-1','toy_witness':toy_w,'toy_ports':toy_p,'toy_parent_same_vector_nonzero':True,'compact_port_scope':'All compact natural K; beta=2^(67*8807)-1; exact symbolic family, no giant integers materialized.','lean_executed':False,'zero_equivalence_proved':False},sort_keys=True,indent=2))
