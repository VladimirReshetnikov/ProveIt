import mpmath as mp
import sympy as sp
import json
from pathlib import Path

mp.mp.dps=80
g=mp.euler
z2,z3,z4=map(mp.zeta,(2,3,4))

def conv(a,b,n):
    ans=[mp.mpf(0)]*n
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<n:ans[i+j]+=x*y
    return ans

def fp_integral(which,a=mp.mpf(1)/8,M=180):
    # psi = x^-1 * h; psi' = x^-2 * v.
    h=[mp.mpf(-1),-g]+[(-1)**j*mp.zeta(j) for j in range(2,M)]
    if which=='Q5':
        p=[mp.mpf(1)]
        for i in range(5):p=conv(p,h,M)
        integrand=lambda x:mp.digamma(x)**5
    else:
        v=[mp.mpf(1),mp.mpf(0)]+[(j-1)*h[j] for j in range(2,M)]
        p=conv(h,conv(v,v,M),M)
        integrand=lambda x:mp.digamma(x)*mp.polygamma(1,x)**2
    base=sum(c*a**(j-4)/(j-4) if j!=4 else c*mp.log(a) for j,c in enumerate(p))
    return base+mp.quad(integrand,[a,mp.mpf('.25'),mp.mpf('.5'),1])

y,L,Z2=sp.symbols('y L Z2')
def asymptotic_poly(which,K):
    b=L-y/2-sum(sp.bernoulli(2*k)*y**(2*k)/(2*k) for k in range(1,K+1))
    p=y+y*y/2+sum(sp.bernoulli(2*k)*y**(2*k+1) for k in range(1,K+1))
    pp=-y*y-y**3-sum((2*k+1)*sp.bernoulli(2*k)*y**(2*k+2) for k in range(1,K+1))
    c=2*Z2-p; d=pp/2
    if which=='Q5':P=20*(b**3-3*b*c+d-L**3+6*Z2*L)*L*y-20*b*L*y**3-10*c*L*y**2
    else:P=-4*d*L*y-4*b*L*y**3-2*c*L*y**2
    # Removing terms of exponent > 2K retains a controlled asymptotic prefix.
    return [((int(p),int(q)),coef) for (p,q),coef in sp.Poly(sp.expand(P),y,L).terms() if p<=2*K]

deriv_cache={}
def zder(p,q,N):
    key=(p,q,N)
    if key not in deriv_cache:deriv_cache[key]=mp.diff(lambda s:mp.zeta(s,N),p,q)
    return deriv_cache[key]

def arithmetic(which,N=64,K=16):
    if which=='Q5':
        val=30*g*g*z2-60*g*z3+mp.mpf(35)/3*z4+20*mp.stieltjes(4)-120*z2*mp.stieltjes(2)
    else:val=-2*g*z3+mp.mpf(35)/6*z4
    for n in range(1,N):
        n=mp.mpf(n);l=mp.log(n);b=mp.digamma(n);p=mp.polygamma(1,n);d=mp.polygamma(2,n)/2;c=2*z2-p
        if which=='Q5':val+=20*(b**3-3*b*c+d-l**3+6*z2*l)*l/n-20*b*l/n**3-10*c*l/n**2
        else:val-=4*d*l/n+4*b*l/n**3+2*c*l/n**2
    for (p,q),coef in asymptotic_poly(which,K):
        cv=mp.mpf(str(sp.N(coef.subs(Z2,sp.Float(str(z2),90)),90)))
        val+=cv*(-1)**q*zder(p,q,N)
    return val

if __name__=='__main__':
    results={}
    for which in ['I','Q5']:
        iv1=fp_integral(which);iv2=fp_integral(which,mp.mpf(1)/16)
        av1=arithmetic(which,48,14);av2=arithmetic(which,64,16)
        entry={'direct_1_over_8':mp.nstr(iv1,77),'direct_1_over_16':mp.nstr(iv2,77),'arithmetic_48_14':mp.nstr(av1,77),'arithmetic_64_16':mp.nstr(av2,77),'direct_difference':mp.nstr(abs(iv1-iv2),10),'residual_48_14':mp.nstr(abs(iv1-av1),10),'residual_64_16':mp.nstr(abs(iv1-av2),10)}
        results[which]=entry
        print(which,json.dumps(entry,indent=2),flush=True)
    with open(Path(__file__).resolve().parent.parent / 'results' / 'fifth_numeric_results.json','w') as out:json.dump(results,out,indent=2)
