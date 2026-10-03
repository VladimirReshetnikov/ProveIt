"""Independent low-order derivation using direct cumulant differentiation,
partition-enumerated Gaussian moments, and direct convergent Fuss sums.
Never imports or calls the coefficient generator.
"""
import math,json,itertools
from pathlib import Path
import mpmath as mp
mp.mp.dps=100
BASE=Path(__file__).resolve().parent.parent

def pmul(a,b,N):
 return [sum(a[i]*b[j-i] for i in range(max(0,j-len(b)+1),min(j+1,len(a)))) for j in range(N+1)]
def pdiv(a,b,N):
 q=[mp.mpf(0)]*(N+1)
 for j in range(N+1):q[j]=(a[j] if j<len(a) else 0)-sum(b[i]*q[j-i] for i in range(1,min(j+1,len(b)))) ;q[j]/=b[0]
 return q

def weighted_parts(weight, largest):
 if largest==0:
  if weight==0:yield []
  return
 for x in range(weight//largest+1):
  for prev in weighted_parts(weight-x*largest,largest-1):yield prev+[x]

def saddle(derivatives,g_taylor,order):
 # g_taylor is Taylor coefficients of the amplitude g(t exp(s)), not log g.
 # Enumerate each Gaussian monomial independently, avoiding an exp recurrence.
 out=[];sig=derivatives[2]
 for j in range(order+1):
  total=mp.mpf(0)
  for ell in range(2*j+1):
   for parts in weighted_parts(2*j-ell,2*j):
    deg=ell+sum((i+3)*a for i,a in enumerate(parts))
    if deg%2:continue
    value=g_taylor[ell]*(-1)**(deg//2)*mp.factorial(deg)/(2**(deg//2)*mp.factorial(deg//2))*sig**(-mp.mpf(deg)/2)
    for i,a in enumerate(parts):
     m=i+3
     value*= (derivatives[m]/math.factorial(m))**a/math.factorial(a)
    total+=value
  out.append(total)
 return out

def derive(k):
 d=k-1;t=k+mp.lambertw(-k*mp.e**(-k)) # positive root
 rho=mp.exp(-t);v=t/k;c=1-k*rho;q=rho*v**d
 kap=[mp.diff(lambda s:mp.log(mp.expm1(t*mp.exp(s))),0,m) for m in range(9)]
 S=saddle(kap,[mp.mpf(1)]+[mp.mpf(0)]*6,3)
 f1=(mp.mpf(1)/k-1)/12
 tau1=S[1]+f1
 tau2=S[2]+f1*S[1]+f1*f1/2
 # Direct summation of binomial(kr,r)q^r; independent of the generator's
 # derivative-polynomial Fuss moment recurrence.
 M=[sum(mp.mpf(math.comb(k*r,r))*q**r*r**j for r in range(1,1200)) for j in range(5)]
 G2=d*(d+1)*M[3]/24+(9-d)*M[2]/24+tau1*M[1]
 G3=d*(d+1)*M[4]/16+(5-d)*M[3]/16+3*tau1*M[2]/2+(2*tau2-tau1*tau1)*M[1]
 # Only h<=floor(3/d) is relevant. Exact P_h values from the defining
 # A recurrence, kept here independently and checked at small indices.
 H=3//d;A=[0]*(H+1);P=[0]*(H+1)
 for n in range(1,H+1):
  A[n]=n**(k*n)-sum(math.comb(n,h)*n**(k*(n-h))*A[h] for h in range(1,n))
  P[n]=mp.mpf(A[n])/math.factorial(n)
 source=[mp.mpf(0)]*4
 for h in range(1,H+1):
  N=3-d*h
  # Multiplier g(z)=exp(hz)*(z^k/(exp(z)-1))^h normalized at saddle.
  logg=lambda s:h*t*(mp.exp(s)-1)+k*h*s-h*(mp.log(mp.expm1(t*mp.exp(s)))-mp.log(mp.expm1(t)))
  gt=mp.taylor(lambda s:mp.exp(logg(s)),0,2*N)
  rel=pdiv(saddle(kap,gt,N),S,N)
  # Factorial prefactor exactly as a Taylor expansion of its rational function.
  rational=lambda x:mp.fprod(1-i*x for i in range(h))/mp.fprod(1-mp.mpf(i)/k*x for i in range(k*h))
  fact=mp.taylor(rational,0,N)
  rel=pmul(rel,fact,N)
  for j,r in enumerate(rel):source[d*h+j]+=P[h]*v**(d*h)*r
 p0=c;p1=-k*rho*v/(2*c)-source[1]*c
 p2=-c*(c*G2+mp.mpf(3)/2*p1*M[1]+source[2])
 p3=-c*(c*G3+p1*(G2+mp.mpf(3)/2*M[2])+mp.mpf(5)/2*p2*M[1]+source[3])
 p=[p0,p1,p2,p3]
 if k==2:
  b=[c,p1+q*c,p2+q*p1+c*(q+5*q*q),p3+q*p2+(2*q+5*q*q)*p1+c*(q*(mp.mpf(11)/12+tau1)+15*q*q+54*q**3)]
 elif k==3:b=[c,p1,p2+q*c,p3+q*(p1+mp.mpf(3)/2*c)]
 elif k==4:b=[c,p1,p2,p3+q*c]
 else:b=p.copy()
 ref=json.loads((BASE/f'coefficients_k{k}.json').read_text())
 out={'k':k,'t':str(t),'p_independent':[mp.nstr(x,80) for x in p],'b_independent':[mp.nstr(x,80) for x in b],'tau_independent':[mp.nstr(x,80) for x in [1,tau1,tau2]],'source_independent':[mp.nstr(x,80) for x in source]}
 out['differences']={label:[mp.nstr(x-mp.mpf(y),10) for x,y in zip(values,ref[label])] for label,values in [('p',p),('b',b),('tau',[1,tau1,tau2]),('small_boundary_source',source)]}
 out['moment_checks']={'M0':mp.nstr(M[0]-(1/c-1),10),'M1':mp.nstr(M[1]-k*rho*v/c**3,10)}
 return out

if __name__=='__main__':
 out=[]
 for k in (2,3,4):
  result=derive(k);out.append(result);print(k,json.dumps(result['differences']),flush=True)
 (BASE/'independent_checks'/'low_orders.json').write_text(json.dumps(out,indent=2)+'\n')
