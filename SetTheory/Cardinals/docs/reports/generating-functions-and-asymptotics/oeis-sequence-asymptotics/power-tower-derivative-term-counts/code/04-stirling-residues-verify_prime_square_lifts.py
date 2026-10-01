from fractions import Fraction as Q
from pathlib import Path
import json
primes=[3,5,7,11]
R=max(p*p-1 for p in primes)
h=[Q(1)]+[Q((-1)**(j-1),j*(j+1)) for j in range(1,R+1)]
logh=[Q(0)]
for n in range(1,R+1):logh.append(h[n]-sum((j*logh[j]*h[n-j] for j in range(1,n)),Q(0))/n)
polys=[[Q(1)]];out=[]
for n in range(1,R+1):
 row=[Q(0)]*(n+1)
 for j in range(1,n+1):
  for k,c in enumerate(polys[n-j]):row[k+1]+=j*logh[j]*c/n
 polys.append(row)
 for p in primes:
  if n!=p*p-1:continue
  mod=p**3
  co=[p**(p+2)*q for q in row[1:]]
  cc=[int(q.numerator)*pow(int(q.denominator),-1,mod)%mod for q in co]
  def ev(x):
   y=0
   for c in reversed(cc):y=(y*x+c)%mod
   return y
  roots=list(range(p));base=p
  for _ in range(2):
   roots=[next(a+t*base for t in range(p) if ev(a+t*base)%(base*p)==0) for a in roots];base*=p
  expected=[(p-p*p)%mod]+list(range(1,p))
  if roots!=expected:raise RuntimeError(('prime-square lifts',p,roots,expected))
  record={'p':p,'roots_mod_p3':roots,'expected_roots':expected,'all_pass':True}
  out.append(record);print(record,flush=True)
Path(__file__).with_name('prime_square_lifts.json').write_text(json.dumps(out,indent=2)+'\n')
