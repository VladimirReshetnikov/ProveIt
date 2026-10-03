"""Exact integer recurrence through n=2500 compared with two corrections."""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=70
row=[1]; out=[]
for n in range(1,2501):
 nxt=[0]*(n+1); tail=0
 for k in range(n,0,-1):
  if k<len(row): tail+=row[k]
  nxt[k]=row[k-1]+k*tail
 row=nxt
 if n in [50,100,200,400,800,1600,2500]:
  a=sum(row); w=mp.lambertw(mp.mpf(n)/mp.e); r=mp.mpf(n)/w
  logmain=-2+(n-mp.mpf('1.5'))*mp.log(r)+r-n-mp.log(2*mp.pi*(w+1))/2
  ratio=mp.exp(mp.log(mp.mpf(a))-logmain)
  c1=(20*w**3+86*w*w+128*w+67)/(24*(w+1)**3)
  c2=(1168*w**6+9968*w**5+34692*w**4+64536*w**3+69380*w**2+42208*w+11857)/(1152*(w+1)**6)
  record={'n':n,'r':str(r),'ratio':str(ratio),'scaled_first':str(r*(ratio-1)),'c1':str(c1),'scaled_second':str(r*r*(ratio-1-c1/r)),'c2':str(c2),'second_difference':str(r*r*(ratio-1-c1/r)-c2)}
  out.append(record);print(n,mp.nstr(ratio,20),mp.nstr(c1,20),mp.nstr(r*r*(ratio-1-c1/r),20),flush=True)
Path('coefficient_checks.json').write_text(json.dumps(out,indent=2))
