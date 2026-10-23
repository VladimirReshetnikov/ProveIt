if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Independent exact degree and algebra audit for new magnitude-companion finalizer."""
from pathlib import Path
from collections import Counter
import json,random
from independent_review_audit import plus,times
from optimize_nine_circuit import evaluate,audit_body
BASE=Path(__file__).resolve().parent;NINE=BASE.parent/'nine'
class Lead:
 def __init__(self,degree,coeff):self.degree=degree;self.coeff=coeff
 def __add__(self,other):
  if not isinstance(other,Lead):other=scalar(other)
  if not self.coeff:return other
  if not other.coeff:return self
  if self.degree>other.degree:return self
  if self.degree<other.degree:return other
  c=plus(self.coeff,other.coeff)
  if not c:raise ValueError('Exact leading cancellation')
  return Lead(self.degree,c)
 __radd__=__add__
 def __neg__(self):return Lead(self.degree,{m:-v for m,v in self.coeff.items()})
 def __sub__(self,other):return self+-other
 def __mul__(self,other):
  if not isinstance(other,Lead):other=scalar(other)
  return Lead(self.degree+other.degree,times(self.coeff,other.coeff))
 __rmul__=__mul__
 def __pow__(self,n):
  if n==0:return scalar(1)
  if n==1:return self
  q=self**(n//2);q=q*q
  return q*self if n%2 else q
 def record(self):
  return dict(degree=self.degree,leading_coefficient=[dict(coefficient=c,fixed_powers={fixed[i]:e for i,e in enumerate(m) if e}) for m,c in self.coeff.items()])
def scalar(n):return Lead(0,{} if not n else {zero:n})
def lead_values(body):
 global fixed,zero
 fixed=sorted(n['name'] for n in body['nodes'] if n['kind']=='fixed');zero=(0,)*len(fixed);idx={n:i for i,n in enumerate(fixed)}
 values=[];unresolved=[]
 for i,n in enumerate(body['nodes']):
  k=n['kind']
  try:
   if k=='literal':v=scalar(n['value'])
   elif k=='variable':v=Lead(1,{zero:1})
   elif k=='fixed':m=list(zero);m[idx[n['name']]]=1;v=Lead(0,{tuple(m):1})
   else:
    a=values[n['left']];b=values[n['right']]
    if a is None or b is None:v=None
    elif k=='add':v=a+b
    elif k=='sub':v=a-b
    elif k=='mul':v=a*b
  except ValueError:v=None;unresolved.append(i)
  values.append(v)
 return values,unresolved

def alternative(names,leaves):
 A=names['A'];C=names['C'];J=names['J'];D=names['D'];E=names['E'];F=names['F'];G=names['Gp'];H=names['H'];a0=names['a0'];a1=names['a1'];Y=names['Y'];U=names['U'];W=names['W'];V0=names['V0'];V1=names['V1'];c=names['dividend'];d=names['divisor'];n=leaves['n'];i=leaves['i0']+1;j=leaves['j0']+1
 Ab=names['Abar'];Cb=names['Cbar'];Jb=names['Jbar'];Db=names['Dbar'];Eb=names['Ebar'];Fb=names['Fbar'];Gb=names['Gbar'];Hb=names['Hbar'];dr=names['deltaR']
 da=dr*Y*(U+1);dc=2*dr;dj=4*da+10
 dd=da*(Ab+A)*Cb**2+A**2*dc*(Cb+C)+Cb**2+C**2
 de=i*(dj*Db*Cb**2+J*dd*Cb**2+J*D*dc*(Cb+C))
 df=da*(Ab+A)*Eb**2+A**2*de*(Eb+E)+Eb**2+E**2
 dg=da+df*(Cb*Db+1+Ab)+F*(dc*Db+C*dd+Ab+A)
 dh=2*dr+j*dc
 di=dg*(Gb+G)*Hb**2+G**2*dh*(Hb+H)+Hb**2+H**2
 m1=(Ab+1)*Cb+1;m2=(Ab+1)*Eb+1;m3=(Gb+1)*Hb+1
 dm1=dd+2*Ab*Cb**2+2*(Ab+1)*Cb
 dm2=df+2*Ab*Eb**2+2*(Ab+1)*Eb
 dm3=di+2*Gb*Hb**2+2*(Gb+1)*Hb
 S=dm1*m2**2*m3**2+D*dm2*m3**2+D*F*dm3+2*m1*m2*m3+1
 E0=d*n+c-W*c
 inner=E0**2-2*E0*W*V0*V1+W**2*V0**2*S-W**2*a0
 out=inner**2-4*W**4*V0**2*a0*a1
 return dict(deltaA=da,deltaC=dc,deltaJ=dj,deltaD=dd,deltaE=de,deltaF=df,deltaG=dg,deltaH=dh,deltaI=di,m1=m1,m2=m2,m3=m3,V1square_minus_a1=S,E0=E0,inner_rewritten=inner,output_rewritten=out)

if __name__=='__main__':
 raise SystemExit('Use the top-level verify_release.py for the selected final candidate.')
