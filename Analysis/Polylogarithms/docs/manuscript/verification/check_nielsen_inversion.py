"""Defining-integral checks of the finite inversion compiler."""
from pathlib import Path
from functools import lru_cache
from math import comb,factorial
import json
import mpmath as m
m.mp.dps=55
@lru_cache(maxsize=None)
def S(n,p,z):
    return (-1)**(n+p-1)*m.quad(lambda t:m.log(t)**(n-1)*m.log(1-z*t)**p/t,[0,1])/(factorial(n-1)*factorial(p))
def compiled(n,p,z):
    u=m.log(-z)
    right=u**(n+p)/factorial(n+p)
    right+=m.fsum((-1)**ell*comb(n+ell-1,ell)*u**(p-r-ell)/factorial(p-r-ell)*S(n+ell,r,z)
                  for r in range(1,p+1) for ell in range(p-r+1))
    right*=(-1)**n
    for j in range(n):
        endpoint=(-1)**j*S(n-j,p,m.mpf(-1))-(-1)**n*m.fsum(
            (-1)**(p-r)*comb(n-j+p-r-1,p-r)*S(n-j+p-r,r,m.mpf(-1)) for r in range(1,p+1))
        right+=endpoint*u**j/factorial(j)
    return right
checks=[]
for n,p in ((1,1),(1,2),(2,2),(3,2)):
    z=-m.mpf(2)/5
    error=abs(S(n,p,1/z)-compiled(n,p,z))
    checks.append(dict(n=n,p=p,z=str(z),residual=m.nstr(error,15),passed=bool(error<m.mpf('1e-45'))))
    print(n,p,checks[-1]['passed'],m.nstr(error,8),flush=True)
result=dict(engine='mpmath '+m.__version__,decimal_digits=55,tolerance='1e-45',checks=checks,all_pass=all(x['passed'] for x in checks))
Path(__file__).with_name('nielsen-inversion-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
raise SystemExit(0 if result['all_pass'] else 1)
