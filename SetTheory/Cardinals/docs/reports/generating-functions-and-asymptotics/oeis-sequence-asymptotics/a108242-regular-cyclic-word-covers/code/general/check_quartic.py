"""Finite/formal quartic diagnostics, not a proof of uniform remainder."""
from itertools import product
from fractions import Fraction
from math import factorial
from pathlib import Path
import sympy as S
import json

def exact_necklace_product(n,r,s):
 words=sorted({min(w[i:]+w[:i] for i in range(4)) for w in product(range(n),repeat=4)})
 vectors=[tuple(w.count(i) for i in range(n)) for w in words]
 cap=(r,)*n;dp={(0,)*n:1}
 for v in vectors:
  out=dict(dp)
  for old,c in dp.items():
   maxj=min((r-old[i])//v[i] for i in range(n) if v[i])
   if s<0:maxj=min(maxj,1)
   for j in range(1,maxj+1):
    t=tuple(old[i]+j*v[i] for i in range(n));out[t]=out.get(t,0)+c
  dp=out
 return dp.get(cap,0),len(words),len(dp)

def main():
 b,c,l,s=S.symbols('b c lambda s');M=4*b+2*c
 singleton=-M/l-S.binomial(M,2)
 one_merger=S.binomial(M,2)
 mode_14=l/2
 E2=S.simplify(singleton+one_merger+mode_14)
 theta=s*l*l/8;eta=l/4
 P2=S.expand(E2.subs({b:theta,c:eta}))
 assert S.simplify(P2.subs(s,1)+S.Rational(1,2))==0
 assert S.simplify(P2.subs(s,-1)-l+S.Rational(1,2))==0
 data={'scope':'Exact finite necklace-product counts and symbolic grade2 check; no empirical uniformity proof.', 'E2':str(E2),'P2_plus':str(P2.subs(s,1)),'P2_minus':str(P2.subs(s,-1)),'counts':[]}
 for n,r in [(1,4),(2,2),(2,4),(3,4),(4,2),(4,4)]:
  N=n*r;B=Fraction(factorial(N),4**(N//4)*factorial(N//4)*factorial(r)**n)
  ap,words,states=exact_necklace_product(n,r,1)
  am,words2,states2=exact_necklace_product(n,r,-1)
  data['counts'].append({'n':n,'r':r,'plus':str(ap),'minus':str(am),'B':str(B),'plus_over_B':str(Fraction(ap)/B),'minus_over_B':str(Fraction(am)/B),'necklace_count':words,'state_count_plus':states})
 Path(__file__).with_name('quartic-results.json').write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps(data,indent=2))
if __name__=='__main__':main()
