"""Exact-coefficient and high-precision saddle checks; diagnostics, not proof."""
if not __debug__:
 raise SystemExit("Do not run this checker with -O or PYTHONOPTIMIZE.")
import argparse, json, math, tempfile
from pathlib import Path
import mpmath as mp
import sympy as sy
BASE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output-dir", help="Directory for a fresh diagnostic receipt; defaults to a new temporary directory.")
args=parser.parse_args()
OUT=Path(args.output_dir).resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix="a301746-check-"))
if OUT==BASE:
 raise SystemExit("Choose a separate output directory; bundled receipts are immutable.")
OUT.mkdir(parents=True,exist_ok=True)
if (OUT/"verification.json").exists():
 raise SystemExit("The destination receipt already exists; choose a fresh output directory.")
mp.mp.dps=55
N=3000
b=[0]*(N+1)
for k in range(1,N+1):
 for j in range(k,N+1,k):b[j]+=1
b=[v*v for v in b]
c=[0]*(N+1)
for k in range(1,N+1):
 for j in range(k,N+1,k):c[j]+=k*b[k]*(1 if (j//k)%2 else -1)
a=[0]*(N+1);a[0]=1
for n in range(1,N+1):
 v=sum(c[j]*a[n-j] for j in range(1,n+1));assert v%n==0;a[n]=v//n
p=sy.symbols('p'); pol=[None,p]
for r in range(2,9):pol.append(sy.expand(p*(1-p)*sy.diff(pol[-1],p)))
polycoeffs=[None]+[[mp.mpf(str(x)) for x in sy.Poly(P,p).all_coeffs()] for P in pol[1:]]
# Conservatively tiny tail; the report does not purport to certify numerical rounding.
def values(t,upto=6):
 K=int(mp.ceil(125/t)); bb=[0]*(K+1)
 for k in range(1,K+1):
  for j in range(k,K+1,k):bb[j]+=1
 ss=[mp.mpf('0')]*(upto+1)
 for k in range(1,K+1):
  weight=bb[k]**2;u=mp.exp(-t*k);p=u/(1+u)
  ss[0]+=weight*mp.log1p(u)
  for r in range(1,upto+1):ss[r]+=weight*k**r*mp.polyval(polycoeffs[r],p)
 return ss
# Use doubles in the root search, then refine in arbitrary precision.
import numpy as np
from scipy.optimize import brentq
def mean_float(t):
 K=int(100/t)+1; ds=np.zeros(K+1,dtype=np.int64)
 for k in range(1,K+1):ds[k::k]+=1
 ks=np.arange(1,K+1,dtype=float)
 return float(np.sum(ds[1:]**2*ks/(1+np.exp(t*ks))))
def multipliers(v):
 V=v[2];k3,k4,k5,k6=v[3:7]
 e1=k4/(8*V**2)-5*k3**2/(24*V**3)
 e2=-k6/(48*V**3)+7*k3*k5/(48*V**4)+35*k4**2/(384*V**4)-35*k3**2*k4/(64*V**5)+385*k3**4/(1152*V**6)
 return e1,e2
Z=[None]+[mp.diff(lambda s:mp.log(mp.zeta(s)),2,j) for j in range(1,4)]
bc=3*mp.euler+mp.log(2)-Z[1]
cc=mp.zeta(2)-2*mp.log(2)**2-3*Z[2]-8*mp.stieltjes(1)-4*mp.euler**2
dc=-2*mp.zeta(3)+6*mp.log(2)**3-7*Z[3]+12*mp.stieltjes(2)+24*mp.euler*mp.stieltjes(1)+8*mp.euler**3
P=lambda L:((L+bc)**3+3*cc*(L+bc)+dc)/12
report={'scope':'Numerical corroboration, not rigorous error certification','constants':{'B1':mp.nstr(bc,45),'B2':mp.nstr(cc,45),'B3':mp.nstr(dc,45)},'initial_terms':a[:36],'eventual_monotonicity_diagnostic':all(a[k+1]>a[k] for k in range(1,N)), 'checks':[]}
for n in [100,300,1000,3000]:
 t=mp.mpf(brentq(lambda t:mean_float(t)-n,0.01,2,xtol=1e-14))
 for _ in range(4):
  v=values(t,2);t+=(v[1]-n)/v[2]
 v=values(t,6);L=mp.log(1/t);M=L**3/t
 logA=v[0]+n*t-mp.log(2*mp.pi*v[2])/2
 delta=mp.log(a[n])-logA;e1,e2=multipliers(v)
 report['checks'].append({'n':n,'t':mp.nstr(t,35),'M':mp.nstr(M,25),'a_over_A0_minus_1':mp.nstr(mp.expm1(delta),35),'E1_minus_1':mp.nstr(e1,35),'a_over_A0_minus_E1':mp.nstr(mp.expm1(delta)-e1,35),'E2_new_term':mp.nstr(e2,35),'a_over_A0_minus_E2':mp.nstr(mp.expm1(delta)-e1-e2,35),'f_minus_main_polynomial':mp.nstr(v[0]-P(L)/t,35),'first_correction_normalized':mp.nstr(e1*M,25)})
 print(n,report['checks'][-1],flush=True)
with (OUT/'verification.json').open('x') as stream:
 stream.write(json.dumps(report,indent=2)+'\n')
print('Saved', OUT/'verification.json')
