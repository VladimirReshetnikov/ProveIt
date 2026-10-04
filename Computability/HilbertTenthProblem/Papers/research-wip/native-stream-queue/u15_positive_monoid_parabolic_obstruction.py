#!/usr/bin/env python3
"""Fresh exact algebra supporting the positive-monoid GL2 obstruction."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
 'u15_faithful_parabolic_obstruction.md': '4ae00a2f43e7bda8163f7fa525605848a25647e9d7b68e393d94b0a0d4068e65',
 'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
}
NAMES = ('s','t','x','z','u','m')
ZERO = (0,) * len(NAMES)

def need(ok,msg):
 if not ok: raise ValueError(msg)

def sha(raw): return hashlib.sha256(raw).hexdigest()

def pairs(items):
 out={}
 for k,v in items:
  need(k not in out,'duplicate JSON key'); out[k]=v
 return out

def bad_constant(value): raise ValueError('nonfinite JSON '+value)
def read(path): return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad_constant)
def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

class Poly(dict):
 def __init__(self,value=0):
  super().__init__(value if isinstance(value,dict) else ({ZERO:value} if value else {}))
 def __add__(self,other):
  out=Poly(self)
  for k,v in Poly(other).items():
   out[k]=out.get(k,0)+v
   if not out[k]: del out[k]
  return out
 __radd__=__add__
 def __neg__(self): return Poly({k:-v for k,v in self.items()})
 def __sub__(self,other): return self+-Poly(other)
 def __rsub__(self,other): return Poly(other)+-self
 def __mul__(self,other):
  out=Poly()
  for a,u in self.items():
   for b,v in Poly(other).items():
    key=tuple(x+y for x,y in zip(a,b)); out[key]=out.get(key,0)+u*v
  return Poly({k:v for k,v in out.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  need(type(n) is int and n>=0,'nonnegative polynomial power')
  result=Poly(1)
  for _ in range(n): result=result*self
  return result
 def put(self,index,value):
  out=Poly()
  for key,c in self.items():
   rest=list(key); rest[index]=0
   out+=Poly({tuple(rest):c})*Poly(value)**key[index]
  return out
 def terms(self): return [[list(k),v] for k,v in sorted(self.items())]

def var(name):
 key=[0]*len(NAMES); key[NAMES.index(name)]=1; return Poly({tuple(key):1})

I=(1,0,0,1)
def mul(a,b):
 x,y,z,t=a; u,v,w,s=b
 return x*u+y*w,x*v+y*s,z*u+t*w,z*v+t*s

def det(a): return a[0]*a[3]-a[1]*a[2]
def inv(a):
 d=det(a); need(d in (-1,1),'GL2 inverse')
 return d*a[3],-d*a[1],-d*a[2],d*a[0]
def power(a,n):
 if n<0: a=inv(a); n=-n
 out=I
 while n:
  if n&1: out=mul(out,a)
  a=mul(a,a); n//=2
 return out

def tr(a): return a[0]+a[3]
def matrix(a): return [list(a[:2]),list(a[2:])]
def word(w,a,b):
 out=I
 for letter in w: out=mul(out,a if letter=='a' else b)
 return out

def verify(root):
 for name,pin in PINS.items(): need(sha((root/name).read_bytes())==pin,'proof pin '+name)
 s,t,x,z,u,m=map(var,NAMES); identities=[]
 def equality(label,left,right):
  need(left==right,label)
  identities.append({'name':label,'terms':Poly(right).terms()})
 # Cayley--Hamilton for determinant -1 gives A^-1=A-sI and B^-1=B-tI.
 comm_from_CH=(x*x-2)-t*(s*x+t)-s*(t*x+s)+s*t*x
 K=x*x-s*t*x-s*s-t*t-2
 equality('commutator trace from Cayley-Hamilton',comm_from_CH,K)
 y0,y1=t,x*t+s
 y2=x*y1-y0; y3=x*y2-y1
 W=(t*t+1)*x**3+s*t*x*x-(2*t*t+3)*x-s*t
 equality('W trace from X recurrence',t*y3+(x**3-3*x),W)
 equality('x=-2 trace boundary',W.put(2,-2),3*s*t-4*t*t-2)
 equality('x=-2 odd trace boundary',y3.put(2,-2),3*s-4*t)
 D=z*z-1
 for epsilon in (-1,1):
  N=z**3-3*z+2*epsilon
  num=z*(z*z-2)*t*t+N
  equality('N factor epsilon '+str(epsilon),N,(z-epsilon)**2*(z+2*epsilon))
  # Substituting s=num/(tD) into K-2 and clearing its nonzero denominator.
  cleared=(z*z-t*t-4)*t*t*D*D-num*num+z*num*t*t*D
  equality('cleared Fricke square epsilon '+str(epsilon),cleared,-(t*t+epsilon*N)**2)
  monic=u*u-m*(z+epsilon)*u+epsilon*(z+2*epsilon)
  numerator=(t*t+epsilon*N-m*t*D).put(1,(z-epsilon)*u)
  equality('monic root scaling epsilon '+str(epsilon),numerator,(z-epsilon)**2*monic)
 fixtures=[]
 def fixture(label,a,b,forced=None):
  need(det(a)==det(b)==-1 and tr(a)>0 and tr(b)>0,'fixture determinants/traces')
  X=mul(a,b); w=word('abababbb',a,b); k=mul(mul(mul(a,b),inv(a)),inv(b))
  sv,tv,xv=tr(a),tr(b),tr(X)
  need(tr(w)==(tv*tv+1)*xv**3+sv*tv*xv*xv-(2*tv*tv+3)*xv-sv*tv,'matrix W trace')
  need(tr(k)==xv*xv-sv*tv*xv-sv*sv-tv*tv-2,'matrix Fricke trace')
  item={'label':label,'A':matrix(a),'B':matrix(b),'traces':[sv,tv,xv],'W':matrix(w),'commutator_trace':tr(k)}
  if forced:
   g=word(forced,a,b)
   need(det(g)==-1 and tr(g)==0 and mul(g,g)==I,'positive involution')
   item.update({'positive_involution_word':forced,'involution':matrix(g)})
  else:
   need(mul(a,b)==mul(b,a) and w==tuple(-v for v in I),'commuting W=-I')
  fixtures.append(item)
 # Both exceptional trace pairs are realized, but neither is monoid-faithful.
 U=(-1,1,1,0); V=(0,-1,-1,-2)
 for u0,v0,label,forced in ((U,V,'epsilon+ u2','abbabbababb'),(V,U,'epsilon+ u3','abbababbababb')):
  X=mul(v0,inv(u0)); b=mul(inv(X),u0); a=mul(X,inv(b))
  need(mul(X,b)==u0 and mul(X,mul(X,b))==v0,'exceptional reconstruction')
  fixture(label,a,b,forced)
 need(fixtures[0]['traces']==[23,6,-4] and fixtures[1]['traces']==[34,9,-4],'exhaustive exceptional trace values')
 for value in (1,2,3,4):
  H=(value,1,1,0); a=tuple(-v for v in power(H,-5)); b=power(H,3)
  fixture('epsilon- commuting u'+str(value),a,b)
 fixture('x=-2 boundary',(0,-1,-1,4),(3,1,1,0),'abababb')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'word':'abababbb','polynomial_variables':list(NAMES),'formal_identities':identities,'exact_matrix_fixtures':fixtures,'evidence':{'formal_polynomial_identities':len(identities),'exact_matrix_fixtures':len(fixtures),'exceptional_trace_pairs':2,'commuting_family_fixtures':4,'positive_involutions':3},'scope':'Formal trace identities and explicit nonfaithful examples; the unrestricted integral classification and geometric SL2 case are proved in the companion, not inferred from finite sampling.','new_universal_Diophantine_bound':False,'predecessor_code_executed':False}

def main():
 parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--root',type=Path,required=True)
 mode=parser.add_mutually_exclusive_group(required=True); mode.add_argument('--expect',type=Path); mode.add_argument('--output',type=Path); args=parser.parse_args()
 result=verify(args.root.resolve())
 if args.expect: need(exact(result,read(args.expect)),'type-exact receipt')
 else: args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','evidence':result['evidence']},sort_keys=True))
if __name__=='__main__': main()
