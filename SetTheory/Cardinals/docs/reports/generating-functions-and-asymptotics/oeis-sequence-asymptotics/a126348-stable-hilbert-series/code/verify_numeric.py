import mpmath as mp
import json,time
from pathlib import Path
mp.mp.dps=70
N=2000
v=[0]*(N+1);v[0]=1
for k in range(1,N+1):
 old=v[:]; cs=0
 for n in range(k,N+1):
  cs+=old[n-k]
  v[n]+=cs
need=[1,1,2,4,7,12,20,33,53,84,131]
if v[:len(need)]!=need: raise RuntimeError('initial coefficients')
c=mp.pi**2/6
def data(n):
 L=mp.findroot(lambda L:mp.exp(2*L)*(L*L/2+L+c)-n, max(mp.mpf('.1'),mp.log(n)/2-mp.log(mp.log(n))))
 t=mp.exp(-L); V=[L*L/2+c,L*L/2+L+c,L*L+3*L+2*c+1,3*L*L+11*L+6*c+6,12*L*L+50*L+24*c+35]
 # recurrence V_j=jV_(j-1)+V'_(j-1) for quadratics
 a,b,d=12,50,24*c+35
 for j in range(5,7): a,b,d=j*a,j*b+2*a,j*d+b; V.append(a*L*L+b*L+d)
 E1=V[4]/(8*V[2]**2)-5*V[3]**2/(24*V[2]**3)
 E2=-V[6]/(48*V[2]**3)+7*V[3]*V[5]/(48*V[2]**4)+35*V[4]**2/(384*V[2]**4)-35*V[3]**2*V[4]/(64*V[2]**5)+385*V[3]**4/(1152*V[2]**6)
 p1=(5-L)/24;p2=-mp.mpf(1)/9
 C1=p1+E1
 C2=p2+p1*p1/2+p1*E1+E2-1/(48*V[2])-(6-L)*V[3]/(48*V[2]**2)
 phase=mp.exp(L)*(L*L+L+2*c)-1-mp.log(2*mp.pi*mp.exp(3*L)*V[2])/2
 ratio=mp.exp(mp.log(v[n])-phase)
 return {'n':n,'L':str(L),'ratio':str(ratio),'C1':str(C1),'C2':str(C2),'error0':str(ratio-1),'error1':str(ratio-1-t*C1),'error2':str(ratio-1-t*C1-t*t*C2),'error2_over_t3L3':str((ratio-1-t*C1-t*t*C2)/(t**3*L**3))}
rows=[data(n) for n in [50,100,200,500,1000,2000]]
print(json.dumps(rows,indent=2));Path('numeric_results.json').write_text(json.dumps(rows,indent=2))
