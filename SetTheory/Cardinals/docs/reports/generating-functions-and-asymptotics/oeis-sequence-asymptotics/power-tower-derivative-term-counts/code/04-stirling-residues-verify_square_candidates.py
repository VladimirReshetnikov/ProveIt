from fractions import Fraction as Q
from pathlib import Path
import json
primes=[3,5,7,11,13,17,19]
R=max((p-1)**2 for p in primes)
h=[Q(1)]+[Q((-1)**(j-1),j*(j+1)) for j in range(1,R+1)]
l=[Q(0)]
for n in range(1,R+1):l.append(h[n]-sum((j*l[j]*h[n-j] for j in range(1,n)),Q(0))/n)
out=[]
for p in primes:
 m=p-1;r=m*m;a=p*p+p-2;v=[Q(1)]
 for n in range(1,r+1):v.append(a*sum((j*l[j]*v[n-j] for j in range(1,n+1)),Q(0))/n)
 g=p**m*v[r]
 mod=p**4;res=g.numerator*pow(g.denominator,-1,mod)%mod
 if res%p**3:raise RuntimeError((p,'not p3'))
 c=(-m*(res//p**3))%p
 if not v[r]:raise RuntimeError(('unexpected zero candidate',p))
 rec={'p':p,'r':r,'candidate':a,'coefficient_numerator':str(v[r].numerator),'coefficient_denominator':str(v[r].denominator),'exact_value_nonzero':True}
 out.append(rec);print(rec,flush=True)
Path(__file__).with_name('square_candidates.json').write_text(json.dumps(out,indent=2)+'\n')
