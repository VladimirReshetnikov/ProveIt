from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
import math,json
import mpmath as mp
mp.mp.dps=60
NMAX=1000
phi=list(range(NMAX+1))
for p in range(2,NMAX+1):
 if phi[p]==p:
  for k in range(p,NMAX+1,p):phi[k]-=phi[k]//p
N=[0]*(NMAX+1)
for d in range(1,NMAX+1):
 b=math.comb(2*d,d)
 for n in range(d,NMAX+1,d):N[n]+=(-1)**(n+d)*phi[n//d]*b
for n in range(1,NMAX+1):N[n]//=2*n
S=[1]+[0]*NMAX
I=[0]*(NMAX+1)
for n in range(1,NMAX+1):
 S[n]=sum(N[k]*S[n-k] for k in range(1,n+1))//n
 I[n]=S[n]-sum(I[k]*S[n-k] for k in range(1,n))
# evaluate constants through analytic central term, exponentially convergent divisor remainder
R=[mp.mpf(2*n*N[n]-math.comb(2*n,n))/(2*n) for n in range(1,250)]
lam=mp.pi**2/12-mp.log(2)**2+sum(R[n-1]/(n*mp.mpf(4)**n) for n in range(1,250))
mu=mp.log(2)+sum(R[n-1]/mp.mpf(4)**n for n in range(1,250))
out={'lambda':str(lam),'mu':str(mu),'critical_fugacity':str(1/(1-mp.exp(-lam))),'initial_S':S[:33],'initial_I':I[:20],'checks':[]}
for n in [50,100,200,500,1000]:
 row={'n':n}
 for label,arr,sgn in [('score',S,1),('strong',I,-1)]:
  leading=mp.exp(sgn*lam)/(2*mp.sqrt(mp.pi))*mp.mpf(4)**n/n**mp.mpf('2.5')
  c1=-mp.mpf(1)/8+sgn*mp.mpf(5)/2*mu
  err=mp.mpf(arr[n])/leading-1-c1/n
  row[label+'_scaled_second_residual']=str(n*n*err)
 out['checks'].append(row)
print(json.dumps(out,indent=2));open(str(RESULT_DIR / 'score-checks.json'),'w').write(json.dumps(out,indent=2))
