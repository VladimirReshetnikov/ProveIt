"""Independent cubic-ray numerical diagnostics, not interval certificates.
This computes T from its Mellin series, obtains Omega3 and J3 there, then
checks the proved formula on six additional rays. The first-derivative
subtraction only uses the already exact lower directional layer.
"""
from pathlib import Path
import json,time
import tornheim_mellin as mod
import mpmath as mp
mp.mp.dps=65
mod.K=56;mod.N=140
start=time.time()
def derivative3(raw):
 a,b,c=map(mp.mpf,raw)
 xs=[];ys=[]
 first=mod.prediction(a,b,c)[1]
 for j in range(7):
  h=mp.mpf('0.002')/2**j
  plus=mod.tornheim(a*h,b*h,c*h);minus=mod.tornheim(-a*h,-b*h,-c*h)
  xs.append(h*h);ys.append(3*(plus-minus-2*h*first)/h**3)
 return mod.extrapolate_zero(xs,ys)
L=mp.log(2*mp.pi);p2=mp.zeta(0,derivative=2);p3=mp.zeta(0,derivative=3);q3=mp.zeta(-1,derivative=3)
omega=derivative3((1,1,1));J=derivative3((1,0,2));kappa=J+mp.mpf(35)/2*p3+6*L*p2-9*q3
print('Omega,J,kappa',*[mp.nstr(v,55) for v in [omega,J,kappa]],flush=True)
rows=[]
for raw in [(1,2,3),(2,3,1),(1,1,2),(1,-2,3),(0,0,1),(1,0,1)]:
 a,b,c=map(mp.mpf,raw);S=a+b+c;B=c*(c*c+a*b-a*a-b*b)/((a+c)*(b+c));D=a*a+b*b-c*(a+b)
 pred=a*b*c*omega-c*D*kappa/2+(8*a*b*c-((a+c)**3+(b+c)**3)/2)*p3
 pred-=mp.mpf('1.5')*((a+b)*(a*b+c*c)-4*a*b*c)*L*p2
 pred+=S*S*B*q3
 num=derivative3(raw)
 assert abs(pred-num) < mp.mpf('1e-34')
 row={'slopes':raw,'formula':mp.nstr(pred,50),'direct':mp.nstr(num,50),'absolute_error':mp.nstr(abs(pred-num),8)};rows.append(row);print(row,flush=True)
out={'status':'passed', 'qualification':'Uncertified high-precision diagnostics; analytic proof is in the article.', 'dps':mp.mp.dps,'K':mod.K,'N':mod.N,'omega3':mp.nstr(omega,55),'J3':mp.nstr(J,55),'kappa':mp.nstr(kappa,55),'rows':rows,'elapsed':time.time()-start}
Path(__file__).with_name('cubic_numeric.json').write_text(json.dumps(out,indent=2))
