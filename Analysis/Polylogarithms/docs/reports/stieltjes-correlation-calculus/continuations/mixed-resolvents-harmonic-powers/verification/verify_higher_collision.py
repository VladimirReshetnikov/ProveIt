"""Independent finite-part quadrature for one-log cubic Stieltjes collisions.
No use of the proposed collision formula in evaluating the circle integrals.
"""
import mpmath as mp
import json,time
from pathlib import Path
mp.mp.dps=65
DPS=mp.mp.dps
N=190
A=mp.mpf('1.5')
gam=mp.euler
gam1=mp.stieltjes(1)
z2=mp.zeta(2)
z2p=mp.diff(mp.zeta,2)
b1=z2+z2p
coeff=[mp.stieltjes(1,A)]
coeff.extend([(-1)**(r+1)*(mp.harmonic(r)*mp.zeta(r+1,A)+mp.diff(lambda s:mp.zeta(s,A),r+1)) for r in range(1,N+1)])
def h1(x):
    return mp.polyval(list(reversed(coeff)),x-mp.mpf('.5'))
def h0(x): return -mp.digamma(1+x)
def g(m,x):
    if m==0: return -mp.digamma(x)
    return mp.log(x)/x+h1(x)
def h(m,x): return h0(x) if m==0 else h1(x)
def tcoeff(m,a,n=12):
    out=[g(m,a)]
    for r in range(1,n+1):
        zz=mp.zeta(r+1,a)
        out.append((-1)**r*zz if m==0 else (-1)**(r+1)*(mp.harmonic(r)*zz+mp.diff(lambda s:mp.zeta(s,a),r+1)))
    return out
def convolution(a,b):
    n=min(len(a),len(b));return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(n)]
def direct_circle(indices,eps):
    shifts=[mp.mpf(0),eps,2*eps]
    points=sorted([(-s)%1 for s in shifts])
    out=mp.mpf(0)
    for j,left in enumerate(points):
        right=points[j+1] if j+1<len(points) else mp.mpf(1)
        length=right-left
        singular=[i for i,s in enumerate(shifts) if abs((left+s)%1)<mp.mpf('1e-60') or abs((left+s)%1-1)<mp.mpf('1e-60')][0]
        others=[i for i in range(3) if i!=singular]
        c=[(left+shifts[i])%1 for i in others]
        tc=convolution(tcoeff(indices[others[0]],c[0]),tcoeff(indices[others[1]],c[1]))
        c0=tc[0]
        threshold=min(c)*mp.mpf('1e-5')
        def f(t):
            if not t: return mp.mpf(0)
            if t<threshold:
                delta=t*mp.polyval(list(reversed(tc[1:])),t)
                prod=c0+delta
            else:
                prod=g(indices[others[0]],c[0]+t)*g(indices[others[1]],c[1]+t)
                delta=prod-c0
            return mp.log(t)**indices[singular]/t*delta+h(indices[singular],t)*prod
        cuts=sorted(set([mp.mpf(0),length]+[t for t in [eps/4,eps,4*eps,length/2] if 0<t<length]))
        out+=mp.quad(f,cuts,method='tanh-sinh')
        out+=c0*mp.log(length)**(indices[singular]+1)/(indices[singular]+1)
    return out
# Direct merged finite part via exactly the local Laurent-log subtraction.
a0=[gam]+[(-1)**r*mp.zeta(r+1) for r in range(1,24)]
b0=[gam1]+[(-1)**(r+1)*(mp.harmonic(r)*mp.zeta(r+1)+mp.diff(mp.zeta,r+1)) for r in range(1,24)]
a2=convolution(a0,a0)
ab=convolution(a0,b0)
a2b=convolution(a2,b0)
def merged_integrand(x):
    L=mp.log(x)
    if x<mp.mpf('1e-6'):
        # (L/x+b)(x^-2+2a/x+a^2), after divergent terms.
        v=L*(2*mp.polyval(list(reversed(a0[2:])),x)+mp.polyval(list(reversed(a2[1:])),x))
        v+=mp.polyval(list(reversed(b0[2:])),x)+2*mp.polyval(list(reversed(ab[1:])),x)+mp.polyval(list(reversed(a2b)),x)
        return v
    aa=h0(x);bb=h1(x)
    return (2*(aa-gam+z2*x)*L/x**2+(aa**2-gam**2)*L/x
            +(bb-gam1-b1*x)/x**2+2*(aa*bb-gam*gam1)/x+aa**2*bb)
Q=-mp.mpf(1)/4-2*gam-gam1+mp.quad(merged_integrand,[0,mp.mpf('.01'),mp.mpf('.2'),1],method='tanh-sinh')
print('Q100',mp.nstr(Q,55),flush=True)
l2=mp.log(2)
def asym(indices,e):
    L=mp.log(e)
    if indices==(1,0,0):
        return ((L*L/4-l2*L/2+z2/2-l2*l2/4)/e**2
          +(3*gam*L*L/4+(gam*l2/2+gam1)*L+3*gam*z2/2+gam*l2*l2/4)/e
          -z2*L*L/4+(z2*l2/2-2*b1)*L+Q-z2*z2/2+z2*l2*l2/4)
    if indices==(0,1,0):
        return ((L*L/2-l2*L/2+z2/4)/e**2
          +(3*gam*L*L/2+gam1*L/2+2*gam*z2+gam1*l2/2)/e
          -z2*L*L/2-b1*L/2+Q-b1*l2/2)
    return (L*L/(2*e**2)
          +(3*gam*L*L/2+(gam*l2+gam1)*L+3*gam*z2/2+gam*l2*l2/2)/e
          +3*z2*L*L/2+b1*L+Q+z2*z2/2)
def T_exact(indices,e):
    L=mp.log(e)
    if indices==(1,0,0):
        return ((L*L/4-l2*L/2+z2/2-l2*l2/4)/e**2
          +h0(e)/e*(z2+L*L/2)+h0(-e)/(2*e)*(z2+(L+l2)**2/2)+h1(-2*e)/e*L)
    if indices==(0,1,0):
        return ((L*L/2-l2*L/2+z2/4)/e**2
          +h0(2*e)/e*(z2+L*L/2)+h0(e)/(2*e)*L*L
          +h1(-e)/(2*e)*(L+l2)+h0(-2*e)/e*(z2+L*L/2))
    return (L*L/(2*e**2)+h1(e)/e*L
       +h0(e)/(2*e)*(z2+(L+l2)**2/2)+h0(-e)/(4*e)*(L+l2)**2
       +h0(-e)/e*(z2+L*L/2)+h0(-2*e)/(2*e)*L*L)
checks=[]
for ind in [(1,0,0),(0,1,0),(0,0,1)]:
    for e in [mp.mpf('0.03'),mp.mpf('0.01'),mp.mpf('0.003'),mp.mpf('0.001'),mp.mpf('0.0003')]:
        start=time.time();c=direct_circle(ind,e);t=T_exact(ind,e);a=asym(ind,e)
        row={'indices':ind,'epsilon':str(e),'C':mp.nstr(c,55),'C_minus_T_minus_Q':mp.nstr(c-t-Q,40),'C_minus_asymptotic':mp.nstr(c-a,40),'seconds':time.time()-start}
        print(row,flush=True);checks.append(row)
record={'dps':DPS,'Q100':mp.nstr(Q,60),'checks':checks,'series_checks':[]}
for x in ['0.12','0.42','0.97','-0.06']:
    xx=mp.mpf(x);res=h1(xx)-mp.stieltjes(1,1+xx)
    record['series_checks'].append({'x':x,'residual':mp.nstr(res,15)})
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2))
