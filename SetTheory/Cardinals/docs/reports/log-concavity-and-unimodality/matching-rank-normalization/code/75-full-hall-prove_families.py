import sympy as s,json
from pathlib import Path
corner_checks=0
verified=[]
from itertools import product
from increment_families import raw,ratios,k,N,K,h,L,z
q,eta,r,J=s.symbols('q eta r J',nonnegative=True)
# Scaling out common balanced moment product; remaining parameters q,eta in[0,1].
def norm(f,lam):
 D=sum(lam)
 if D==1:return s.expand(f).subs({L[0]*L[-1]:1,L[1]*L[-2]:q*(k-1)/(k+1)})
 if D==2:return s.expand(f).subs({L[-1]**2:1,L[0]*L[-2]:q*(k-1)/k,L[1]*L[-3]:q*eta*(k-1)*(k-2)/(k*(k+1))})
 if D==3:return s.expand(f).subs({L[-1]*L[-2]:1,L[0]*L[-3]:q*(k-2)/k})
 if D==4:return s.expand(f).subs({L[-2]**2:1,L[-1]*L[-3]:q*(k-2)/(k-1)})

def positivepoly(expr,sub):
 global corner_checks
 corner_checks+=1
 num,den=s.fraction(s.factor(expr.subs(sub)))
 poly=s.Poly(s.expand(num),J,r,h)
 neg=[(ex,co) for ex,co in poly.terms() if co<0]
 dp=s.Poly(s.expand(den),J,r,h)
 assert all(c>=0 for c in dp.coeffs()) and dp.eval({J:0,r:0,h:0})>0,(num,den)
 return len(neg)==0,s.factor(num),s.factor(den),neg[:2]
if __name__=='__main__':
 for lam in [(1,0),(2,0),(1,1),(2,1),(2,2)]:
  for d in range(sum(lam)):
   f=norm(raw(lam,d).subs(ratios(d)),lam)
   assert not(set(L.values())&f.free_symbols)
   f=s.factor(f.subs(N,k+K-d+h+2))
   allok=True;fails=[]
   for qv,ev,zv in product([0,1],[0,1],[0,s.Rational(1,2)]):
    g=s.factor(f.subs({q:qv,eta:ev,z:zv}))
    # K>=3, k=K+r >=3
    ans=positivepoly(g,{k:J+3+r,K:J+3})
    if not ans[0]:allok=False;fails.append(('K>=3',qv,ev,zv,ans))
    for Kv in range((d+1)//2,3):
     # k>=3; K small fixed
     ans=positivepoly(g,{K:Kv,k:3+r})
     if not ans[0]:allok=False;fails.append((Kv,qv,ev,zv,ans))
   for kv in [1,2]:
    if kv==1 and sum(lam)>=3:
     # Every exterior moment product has a negative-index factor.
     assert s.expand(raw(lam,d).subs({L[a]:0 for a in L if kv+a<0}))==0
     continue
    for Kv in range((d+1)//2,kv+1):
     for qv,ev,zv in product([0,1],[0,1],[0,s.Rational(1,2)]):
      g=s.factor(f.subs({q:qv,eta:ev,z:zv}))
      ans=positivepoly(g,{K:Kv,k:kv})
      if not ans[0]:allok=False;fails.append(('boundary',kv,Kv,qv,ev,zv,ans))
   assert allok,(lam,d,fails)
   verified.append({'left_pattern':lam,'j':d})
   print(lam,d,'PASS'if allok else 'FAIL',flush=True)
   for f in fails[:3]:print(f,flush=True)

 if len(verified)!=12:raise AssertionError(len(verified))
 out={'families_verified':verified,'exact_corner_positivity_checks':corner_checks,'denominators_positive':True,'small_k_and_a_boundaries_verified':True,'all_checks_passed':True}
 Path(__file__).with_name('positivity_verification.json').write_text(json.dumps(out,indent=2)+'\n')
