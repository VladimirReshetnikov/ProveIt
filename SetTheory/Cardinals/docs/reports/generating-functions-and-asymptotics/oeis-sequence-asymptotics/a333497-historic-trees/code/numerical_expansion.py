"""Exploratory high-precision, non-certified numerical validation of A333497.
No fitted value is used to prove any theorem. Constants fitted on disjoint training
indices are checked at further indices. Exact count recurrence is also replayed.
"""
import mpmath as mp, json, math, argparse
from pathlib import Path
import os
P=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).parent))
ap=argparse.ArgumentParser();ap.add_argument('--nmax',type=int,default=1000);ap.add_argument('--dps',type=int,default=100);ap.add_argument('--fit-degree',type=int,default=4);ap.add_argument('--training',default='400,550,700');args=ap.parse_args()
mp.mp.dps=args.dps
lam=(13+mp.sqrt(71)*1j)/2
D=lambda z:(3-z)*(4-z)*(5-z)-120
A={(0,0):mp.mpf(1),(1,0):mp.mpf(1),(0,1):mp.mpf(1)}
for d in range(2,7):
 for k in range(d+1):
  l=d-k; s=0
  for i in range(k+1):
   for j in range(l+1):
    if (i,j) in ((0,0),(k,l)):continue
    s+=A[i,j]*A[k-i,l-j]
  A[k,l]=60*s/D(k*lam+l*mp.conj(lam))
# Scaled ordinary EGF coefficients avoid huge exact factorials.
r0=mp.mpf('3.774627575725')
e=[mp.mpf(1),r0,r0*r0/2]
for n in range(args.nmax-2):
 e.append(r0**3*mp.fsum(e[k]*e[n-k] for k in range(n+1))/((n+1)*(n+2)*(n+3)))

def ratio(n,rho):
 return e[n]*(rho/r0)**n*rho**3/(30*(n+1)*(n+2))

def Q(n,rho,C,degree):
 q=mp.mpc(1)
 for (k,l),a in A.items():
  if not 1<=k+l<=degree or k==l:continue
  nu=k*lam+l*mp.conj(lam)
  q+=2*a*C**k*mp.conj(C)**l*rho**nu*mp.exp(mp.loggamma(n+3-nu)-mp.loggamma(n+3))/mp.gamma(3-nu)
 return mp.re(q)

# Fit three constants rho, Re C, Im C at three training points.
train=list(map(int,args.training.split(',')))
def eq(rho,cre,cim):
 C=mp.mpc(cre,cim)
 return tuple((ratio(n,rho)-Q(n,rho,C,args.fit_degree))*n**mp.mpf('6.5') for n in train)
rho,cre,cim=mp.findroot(eq,(r0,mp.mpf('0.001'),mp.mpf('0.001')),tol=mp.mpf(10)**(-args.dps+15),maxsteps=50)
C=mp.mpc(cre,cim)
serial=lambda z:mp.nstr(z,args.dps-10)
rows=[]
for n in [30,50,75,100,120,160,200,250,300,400,500,600,800,1000]:
 if n>args.nmax:continue
 r=ratio(n,rho)
 rows.append({'n':n,'normalized_minus_one':serial(r-1),'n^6.5_times_normalized_minus_one':serial(n**mp.mpf('6.5')*(r-1)),'relative_error_degree1':serial(r-Q(n,rho,C,1)),'relative_error_degree2':serial(r-Q(n,rho,C,2)),'relative_error_degree3':serial(r-Q(n,rho,C,3)),'relative_error_degree4':serial(r-Q(n,rho,C,4)),'relative_error_degree5':serial(r-Q(n,rho,C,5))})
exact=[1,1,1]
for n in range(100):exact.append(sum(math.comb(n,k)*exact[k]*exact[n-k] for k in range(n+1)))
record={'status':'Exploratory numerical approximations, not interval certified; constants fitted using stated degree at stated training indices','dps':args.dps,'fit_degree':args.fit_degree,'training_indices':train,'rho':serial(rho),'C_real':serial(cre),'C_imag':serial(cim),'lambda':serial(lam),'amplitude_K':serial(2*C*rho**lam/mp.gamma(3-lam)),'psi_coefficients':{str(k):serial(v) for k,v in A.items()},'exact_first30':exact[:30],'checks':rows}
(P/f'numerics_{args.dps}dps.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
