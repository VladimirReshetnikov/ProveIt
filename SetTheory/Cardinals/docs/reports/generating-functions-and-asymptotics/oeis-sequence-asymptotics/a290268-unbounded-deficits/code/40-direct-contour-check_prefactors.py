import mpmath as mp
import json
from pathlib import Path
mp.mp.dps=75


def source(d,k,q):
    R=2*d+q+1
    f=[0]*(d+1);f[0]=1
    for j in range(R):
        a=2*d-j
        for n in range(d,0,-1): f[n]=a*f[n]+f[n-1]
        f[0]*=a
    g0=[1];g1=[2*d-q,2]
    if k==0:g=g0
    elif k==1:g=g1
    else:
        for j in range(1,k):
            g2=[0]*(len(g1)+1)
            for n,x in enumerate(g1):g2[n]+=(2*d-q)*x;g2[n+1]+=2*x
            for n,x in enumerate(g0):g2[n]+=j*(j+R)*x
            g0,g1=g1,g2
        g=g1
    return sum(g[n]*f[d-n] for n in range(min(k,d)+1))


def evaluate(d,k,b):
    q=2*d+b;R=2*d+q+1;M=k+R
    kap=mp.mpf(k)/d;delta=mp.mpf(b)/d;r=4+delta;e=delta/2
    K=lambda T:mp.sin(T)/T-2*mp.cos(T)-2
    T=mp.findroot(lambda T:K(T)-kap,(mp.mpf('2.79'),mp.mpf('2.92')))
    eq=lambda t:mp.sinh(t)/t-r*(1+mp.cosh(t))/2-e*mp.sinh(t)-kap
    t=mp.findroot(eq,-1j*T)
    L=lambda z:mp.log(z)-e*z+kap*mp.log(mp.cosh(z/2))-(kap+r)*mp.log(mp.sinh(z/2))-r*mp.log(2)
    V=t*t*mp.diff(L,t,2)
    P=t/(4*mp.sinh(t/2)**2*mp.sqrt(V))
    new_A=2*mp.factorial(M)/mp.factorial(d)*mp.exp(d*mp.re(L(t)))*abs(P)/mp.sqrt(2*mp.pi*d)
    theta=d*mp.im(L(t))+mp.arg(P)
    x=1/t-e;z=kap/(kap+r)*mp.tanh(t/2);zeta=1/t
    gzz=-(x-r/2)/(1+z)**2+(x+r/2)/(1-z)**2+kap/z**2
    Vi=z*z*gzz
    Vo=1+zeta*zeta*(-r/(x*x-r*r/4)-4/((1-z*z)**2*gzz))
    AF=mp.exp((mp.log(zeta+2)+mp.log(zeta-2-delta))/2)
    Pold=AF/((1-z*z)*mp.sqrt(Vi)*mp.sqrt(Vo))
    S=L(t)+1-r+(kap+r)*mp.log(kap+r)-kap*mp.log(kap)
    f=(zeta+2)*mp.log(zeta+2)-(zeta-2-delta)*mp.log(zeta-2-delta)-r
    g=(zeta-2-delta)*mp.log(1+z)+(-zeta-2)*mp.log(1-z)-kap*mp.log(z)
    Sdirect=f+g-mp.log(zeta)
    if abs(Sdirect-S)>mp.mpf('1e-60'):raise RuntimeError('Action or branch mismatch')
    old_A=mp.mpf(d)**(R-d)*mp.factorial(k)*mp.exp(d*mp.re(S))*abs(Pold)/(mp.pi*d)
    ratio=Pold/P
    target=(kap+r)**mp.mpf('1.5')/mp.sqrt(kap)
    if abs(ratio/target-1)>mp.mpf('1e-60'):raise RuntimeError('Prefactor mismatch')
    H=source(d,k,q)
    normalized=mp.mpf(H)/new_A
    error=normalized-mp.cos(theta)
    return dict(d=d,k=k,b=b,normalized_H=mp.nstr(normalized,24),leading_cosine=mp.nstr(mp.cos(theta),24),scaled_error=mp.nstr(d*error,24),new_over_nested_amplitude=mp.nstr(new_A/old_A,24),prefactor_identity_error=mp.nstr(abs(ratio/target-1),8),direct_nested_action_error=mp.nstr(abs(Sdirect-S),8))

rows=[evaluate(d,d//100,d//200) for d in [200,400,800]]
Path(__file__).with_name('prefactor_checks.json').write_text(json.dumps({'purpose':'Numerical orientation and independent exact integer coefficient comparisons; not a proof of the asymptotic theorem','rows':rows},indent=2)+'\n')
print(json.dumps(rows,indent=2))
