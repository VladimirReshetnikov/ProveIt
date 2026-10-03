from pathlib import Path
"""Exact integer recurrence with mpmath evaluation; evidence, not certification."""
import mpmath as mp, json, time
mp.mp.dps=70
z=mp.airyaizero(1); coeff=[53*z*z/90,271*z/216,mp.mpf(393)/1120-1304*z**3/42525]
rows=[[1],[1,1]]; output=[]
for n in range(2,2501):
 prev=rows[-1];prev2=rows[-2];cur=[1]
 for m in range(1,n+1):
  cur.append(cur[-1]+((m+1)*prev[m] if m<n else 0)-((m-1)*prev2[m-1] if m-1<len(prev2) else 0))
 rows=[prev,cur]
 if n in (20,50,100,200,500,1000,1500,2000,2500):
  logmain=mp.loggamma(n+1)+n*mp.log(4)+3*z*mp.root(n,3)+mp.mpf(3)/4*mp.log(n)
  lg=mp.log(cur[-1])-logmain
  vals=[mp.exp(lg-sum(coeff[k]*mp.power(n,-mp.mpf(k+1)/3) for k in range(m))) for m in range(4)]
  datum={'n':n,'digits':int(mp.log10(cur[-1]))+1,'amplitude_estimates_orders0to3':list(map(str,vals))}
  output.append(datum);print(n,*[mp.nstr(x,18) for x in vals],flush=True)
open(Path(__file__).with_name('forward-check.json'),'w').write(json.dumps({'status':'numerical evidence from exact integer terms, not a rigorous amplitude enclosure','log_coefficients':list(map(str,coeff)),'samples':output},indent=2))
