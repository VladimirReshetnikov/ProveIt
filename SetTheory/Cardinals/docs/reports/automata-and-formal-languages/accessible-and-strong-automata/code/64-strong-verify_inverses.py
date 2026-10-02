"""Numerical checks of smooth asymptotic inverse formulas, without rounding claims."""
from pathlib import Path
import json
import mpmath as mp
from verify_exact_sectors import counts, unrooted
# Importing verify_exact_sectors also reruns its exact assertions.
mp.mp.dps=100
root=Path(__file__).parent
out=[]
for k in [2,3,4]:
    co=json.loads((root/f'coefficients_k{k}.json').read_text());d=k-1
    v=mp.mpf(co['v']);c=k*v-k+1;beta=mp.exp(-d)/((1-v)*v**d)
    C=mp.sqrt(c/(2*mp.pi));alpha=list(map(mp.mpf,co['alpha']))
    _,Labeled=counts(k,240)
    for n in [40,80,120,240]:
        targets={'B':mp.mpf(Labeled[n])/mp.factorial(n), 'R':mp.mpf(Labeled[n])/mp.factorial(n-1)}
        u=unrooted(k,n,Labeled);targets['U']=mp.mpf(u.numerator)/u.denominator
        for mode,X in targets.items():
            s=mp.mpf('.5') if mode=='R' else mp.mpf('-.5')
            y=mp.log(X);x=y/(d*mp.lambertw(beta**(mp.mpf(1)/d)*y/d))
            LL=d*mp.log(x)+d+mp.log(beta);AA=s*mp.log(x)+mp.log(C)
            delta0=-AA/LL
            delta1=-(d*delta0**2/2+s*delta0+alpha[1])/(x*LL)
            inverse2=x+delta0+delta1
            def logmodel(z):
                return mp.log(C)+z*mp.log(beta)+(d*z+s)*mp.log(z)+mp.log(sum(a*z**(-j) for j,a in enumerate(alpha)))
            inv5=mp.findroot(lambda z:logmodel(z)-y,(x,x+1))
            out.append({'k':k,'n':n,'mode':mode,'inverse_two_corrections_error':mp.nstr(inverse2-n,30),
              'scaled_two_corrections_error':mp.nstr((inverse2-n)*n*n*mp.log(n),30),
              'inverse_order5_error':mp.nstr(inv5-n,30),
              'scaled_order5_error':mp.nstr((inv5-n)*n**6*mp.log(n),30)})
(root/'inverse_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Saved 36 smooth-inverse checks for B, rooted R, and unrooted U at k=2,3,4.')
