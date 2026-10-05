from pathlib import Path
import json,mpmath as mp
mp.mp.dps=45
N=10000
a=[0]*(N+1);a[0]=1
for k in range(1,N+1):
 for j in range(N,k-1,-1):a[j]+=k*a[j-k]
expected=[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728,2525,3741,5775,8244,12447]
if a[:len(expected)]!=expected:raise ArithmeticError('OEIS prefix differs')
def ints(b,kind):
 K=mp.exp(b);t=b/K
 def f(x):
  w=x*mp.exp(-t*x);p=w/(1+w)
  return [mp.log1p(w),x*p,x*x*p*(1-p)][kind]
 return mp.quad(f,[0,1,K/2,K,2*K,mp.inf])
rows=[]
for n in [100,1000,10000]:
 B=mp.log(2*n)/2
 b=mp.findroot(lambda b:ints(b,1)-n,(B-mp.mpf('.3'),B))
 K=mp.exp(b);t=b/K;I=ints(b,0);V=ints(b,2)
 pred=I+n*t-1-mp.log(V)/2;actual=mp.log(a[n]);c=mp.pi**2/6
 sj=[c,c,c-c*c/2,c+mp.pi**4/40]
 approx=mp.sqrt(2*n)*(B-1+sum(sj[j-1]/B**j for j in range(1,5)))
 row={'n':n,'exact_a':str(a[n]),'integral_saddle_b':mp.nstr(b,30),'log_relative_prediction_error':mp.nstr(pred-actual,25),'relative_prediction_ratio':mp.nstr(mp.exp(pred-actual),25),'four_term_logarithmic_error':mp.nstr(approx-actual,25)}
 rows.append(row);print(row,flush=True)
out={'status':'Exact coefficient enumeration; integral evaluations are high-precision numerical orientation, not interval certificates.','rows':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
