import mpmath as mp,json
from pathlib import Path
mp.mp.dps=90
c=mp.pi**2/6
P=[lambda L:(5-L)/24,lambda L:-mp.mpf(1)/9,lambda L:(2*L+245)/5760,lambda L:-mp.mpf(11)/900,lambda L:-(8*L+2037)/1451520,lambda L:mp.mpf(341)/52920]
rows=[]
for t in map(mp.mpf,['.5','.25','.1','.05','.02']):
 L=-mp.log(t);d=1-mp.exp(-t);K=int(mp.ceil((L+200)/t))
 exact=mp.fsum(mp.log1p(mp.exp(-k*t)/d) for k in range(1,K+1))
 app=(L*L/2+c)/t-1;err=[]
 for j,p in enumerate(P,1):
  app+=t**j*p(L);err.append(str((exact-app)/t**(j+1)))
 rows.append({'t':str(t),'logF':str(exact),'errors_divided_by_next_power':err,'tail_bound':str(mp.exp(-t*(K+1))/(d*d))})
print(json.dumps(rows,indent=2));Path('product_numeric_results.json').write_text(json.dumps(rows,indent=2))
