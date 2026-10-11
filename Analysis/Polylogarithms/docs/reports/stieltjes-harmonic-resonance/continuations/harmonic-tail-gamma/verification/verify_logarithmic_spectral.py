#!/usr/bin/env python3
"""Exact kernel algebra and independent convergent integral diagnostics."""
import json
from pathlib import Path
import sympy as sp
import mpmath as mp

mp.mp.dps=70
s,L=sp.symbols('s L')
kernel_checks=0
for q in range(1,11):
    closed=(-1)**q*((L+sp.I*sp.pi)**q-(L-sp.I*sp.pi)**q)/(2*sp.I*sp.pi*sp.factorial(q))
    direct=sp.series(-sp.sin(sp.pi*s)/sp.pi*sp.exp(-s*L),s,0,q+1).removeO().coeff(s,q)
    assert sp.expand(closed-direct)==0
    kernel_checks+=1

zcache={j:mp.zeta(j) for j in range(2,140)}
bernoulli={2*j:mp.bernoulli(2*j) for j in range(1,28)}

def scalar_local(x):
    if x<mp.mpf('0.25'):
        return sum((-x)**k*zcache[k+2] for k in range(120))
    return (mp.digamma(1+x)+mp.euler)/x

def scalar_inverted(t):
    # (psi(1+1/t)+log(t))/t, with a small-t asymptotic diagnostic.
    if t<mp.mpf('0.02'):
        return mp.mpf('0.5')-sum(bernoulli[2*j]*t**(2*j-1)/(2*j) for j in range(1,28))
    return (mp.digamma(1+1/t)+mp.log(t))/t

def tri_local(x):
    if x<mp.mpf('0.25'):
        return -2*sum((-x)**k*(k+3)*zcache[k+4] for k in range(120))
    return -2*(mp.polygamma(1,1+x)-zcache[2]+2*zcache[3]*x)/x**2

def tri_inverted(t):
    if t<mp.mpf('0.02'):
        trigamma=t-t*t/2+sum(bernoulli[2*j]*t**(2*j+1) for j in range(1,28))
    else:
        trigamma=mp.polygamma(1,1+1/t)
    return 2*(zcache[2]-trigamma)

def integrate(f):
    return mp.quad(f,[0,mp.mpf('0.02'),mp.mpf('0.25'),1])

moments={}
for name,local,tail,factor in [('digamma_square',scalar_local,scalar_inverted,2),('trigamma_square',tri_local,tri_inverted,1)]:
    moments[name]=[factor*integrate(lambda x: mp.log(x)**r*local(x))+
                   factor*integrate(lambda t: (-mp.log(t))**r*tail(t)) for r in range(4)]

results=[]
for name in moments:
    for q in range(1,5):
        spatial=sum((-1)**(q+m)*mp.pi**(2*m)*moments[name][q-2*m-1]/
                    (mp.factorial(2*m+1)*mp.factorial(q-2*m-1)) for m in range((q-1)//2+1))
        Ks={0:2*mp.euler,1:mp.mpf(2)} if name=='digamma_square' else {0:-4*zcache[3]}
        angular=-sum((-1)**((q+k)//2)*mp.pi**(q+k)*v*mp.factorial(k)/mp.factorial(q+k+1)
                     for k,v in Ks.items() if (q+k)%2==0)
        if name=='digamma_square':
            higher=mp.mpf(0)
            spectral=-2*(-1)**q*mp.stieltjes(q)/mp.factorial(q)
        else:
            higher=2*mp.diff(mp.zeta,3,q-1)/mp.factorial(q-1)
            spectral=4*mp.diff(mp.zeta,3,q)/mp.factorial(q)
        numerical=spatial+angular-higher
        residual=abs(numerical-spectral)
        assert residual<mp.mpf('1e-48'), (name,q,residual)
        results.append({'name':name,'q':q,'spatial':mp.nstr(spatial,55),
                        'angular':mp.nstr(angular,55),'higher_poles':mp.nstr(higher,55),
                        'spectral':mp.nstr(spectral,55),'residual':mp.nstr(residual,8)})

master=[]
spectral_s=mp.mpc('0.27','0.13')
for name,local,tail,factor in [('digamma_square',scalar_local,scalar_inverted,2),('trigamma_square',tri_local,tri_inverted,1)]:
    E=factor*integrate(lambda x:x**(-spectral_s)*local(x))+factor*integrate(lambda t:t**spectral_s*tail(t))
    if name=='digamma_square':
        A=2*mp.euler/spectral_s+2/spectral_s**2
        higher=0
        expected=-2*mp.zeta(1+spectral_s)
    else:
        A=-4*zcache[3]/spectral_s
        higher=2*spectral_s*mp.zeta(3+spectral_s)
        expected=4*mp.zeta(3+spectral_s)
    actual=-mp.sin(mp.pi*spectral_s)/mp.pi*(E+A)-higher
    error=abs(actual-expected)
    assert error<mp.mpf('1e-46'),(name,error)
    master.append({'name':name,'s':str(spectral_s),'residual':mp.nstr(error,8)})

out={'exact_kernel_checks':kernel_checks,'working_digits':mp.mp.dps,
     'quadrature_diagnostics':results,'complex_master_diagnostics':master,
     'scope':'Floating-point diagnostics with local convergent Taylor expansions and small-t asymptotic expansions; not interval certificates.'}
path=Path(__file__).resolve().parent.parent/'data'/'logarithmic_spectral_results.json'
path.write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
