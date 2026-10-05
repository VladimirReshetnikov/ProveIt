import mpmath as mp, json
from pathlib import Path
mp.mp.dps=80
N=10000
v=[0]*(N+1);v[0]=1
for k in range(1,N+1):
 old=v[:]; cs=0
 for n in range(k,N+1):
  cs+=old[n-k];v[n]+=cs
if v[:11]!=[1,1,2,4,7,12,20,33,53,84,131]:raise RuntimeError('initial values')
if not all(v[k]>v[k-1] for k in range(2,N+1)):raise RuntimeError('monotonicity')
c=mp.pi**2/6
def inv(target):
 y=mp.log(target)
 L=mp.findroot(lambda L:mp.exp(L)*(L*L+L+2*c)-y,2*mp.lambertw(mp.sqrt(y)/2))
 A=L*L/2+L+c;V=L*L+3*L+2*c+1
 V3=3*L*L+11*L+6*c+6;V4=12*L*L+50*L+24*c+35
 C1=(5-L)/24+V4/(8*V**2)-5*V3**2/(24*V**3)
 T=1+mp.mpf('1.5')*L+mp.log(2*mp.pi*V)/2
 Tp=mp.mpf('1.5')+(2*L+3)/(2*V)
 x0=mp.exp(2*L)*A;x1=x0+mp.exp(L)*T;x2=x1+(T*T+2*T*Tp)/(2*V)-C1
 return L,x0,x1,x2
out=[]
for n in [50,100,200,500,1000,2000,5000,10000]:
 L,x0,x1,x2=inv(v[n]);row={'n':n,'L':str(L),'core_error':str(x0-n),'first_displacement_error':str(x1-n),'full_formula_error':str(x2-n),'scaled_error':str((x2-n)*mp.exp(L)/(1+L)**3),'rounded_correctly':int(mp.nint(x2))==n};out.append(row)
print(json.dumps(out,indent=2));Path('inverse_numeric_results.json').write_text(json.dumps(out,indent=2))
Path('coefficients_selected.json').write_text(json.dumps({str(n):str(v[n]) for n in [50,100,200,500,1000,2000,5000,10000]},indent=2))
