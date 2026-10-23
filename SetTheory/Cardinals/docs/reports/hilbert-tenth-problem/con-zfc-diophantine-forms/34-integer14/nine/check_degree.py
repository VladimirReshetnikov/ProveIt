"""New exact degree certificate, with algebraic cancellation eliminated explicitly."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
class H:
 def __init__(self,d=0,c=0,dep=False):self.d,self.c,self.dep=d,c,dep
 def __add__(self,b):
  if not isinstance(b,H):b=H(0,b)
  if self.c==0:return b
  if b.c==0:return self
  if self.d>b.d:return self
  if b.d>self.d:return b
  c=self.c+b.c
  if not c:raise ValueError('leading cancellation')
  return H(self.d,c,self.dep or b.dep)
 __radd__=__add__
 def __neg__(self):return H(self.d,-self.c,self.dep)
 def __sub__(self,b):return self+(-b if isinstance(b,H) else -b)
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  if not isinstance(b,H):b=H(0,b)
  return H(self.d+b.d,self.c*b.c,self.dep or b.dep) if self.c and b.c else H()
 __rmul__=__mul__
 def __pow__(self,n):return H(self.d*n,self.c**n,self.dep) if n else H(0,1)
 def rec(self):return {'degree':self.d,'coefficient':self.c,'depends_on_fixed_leading_terms':self.dep}
def heads(body):
 vals=[];bad=[]
 for i,n in enumerate(body['nodes']):
  try:
   k=n['kind']
   if k=='literal':v=H(0,n['value'])
   elif k=='variable':v=H(1,1)
   elif k=='fixed':v=H(0,1,True)
   else:
    a,b=vals[n['left']],vals[n['right']]
    if a is None or b is None:v=None
    elif k=='add':v=a+b
    elif k=='sub':v=a-b
    else:v=a*b
  except ValueError:v=None;bad.append(i)
  vals.append(v)
 return {k:vals[i] for k,i in body['named_nodes'].items()},bad

def rewrite(ns,n):
 A,C,D,E,F,G,Hh=(ns[k] for k in ['A','C','D','E','F','Gp','H'])
 md,mf,mi,r,sig=(ns[k] for k in ['M_D','M_F','M_I','r','sigma'])
 # md = AC + sigma*r^2. We use exact identities, not sampled cancellation.
 dd=2*A*C*sig*r**2+sig**2*r**4+C**2-1
 df=E**2+2*A*E
 # mi - G H: substitute G=FDC+F-A(F-1), tc=CH+r^2.
 diroot=F*D*r**2+2*F*Hh**2+(F-1)*A**2+1-F*Hh+A*(F-1)*Hh
 di=diroot*(mi+G*Hh)+Hh**2-1
 delta=dd*mf**2*mi**2+D*df*mi**2+D*F*di+2*md*mf*mi+1
 u,v,mdiv,om,v0,v1=(ns[k] for k in ['signed_divisor','signed_dividend','M_div','Omega','V0','V1'])
 e0=u*(n+mdiv)+v-2*om*mdiv
 inner=e0**2-2*e0*om*v0*v1+om**2*v0**2*delta-om**2*ns['a0']
 out=inner**2-4*om**4*v0**2*ns['a0']*ns['a1']
 return dict(deltaD=dd,deltaF=df,deltaIRoot=diroot,deltaI=di,V1square_minus_a1=delta,E0=e0,inner=inner,output=out)

def main():
 res={}
 for name in ['nine31_structured','nine31_signed_quadratic']:
  b=json.loads((HERE/(name+'.json')).read_text());ns,bad=heads(b)
  if name.endswith('quadratic'):
   ar=rewrite(ns,H(1,1));o=ar['output'];details={k:v.rec() for k,v in ar.items()}
   assert o.d==92324*b['L']+296,(o.rec(),92324*b['L']+296)
   assert o.c==2**192 and not o.dep,o.rec()
  else:
   o=ns['output'];details={};assert o.d==93264*b['L']+288 and o.c==441*2**188 and not o.dep
  res[name]={'exact_degree':o.d,'leader':o.c,'uniform_independence_of_fixed_coefficients':not o.dep,'named_heads':{k:v.rec() for k,v in ns.items() if v is not None},'rewritten_heads':details,'unresolved_direct_head_nodes':bad}
 (HERE/'DEGREE_CERTIFICATE.json').write_text(json.dumps(res,indent=2)+'\n')
 print(json.dumps({k:{x:v[x] for x in ['exact_degree','leader','uniform_independence_of_fixed_coefficients']} for k,v in res.items()},indent=2))
if __name__=='__main__':main()
