"""Independent quadrature and finite coefficient utilities for the article.

These routines use ordinary mpmath floating-point arithmetic, not interval
arithmetic. Cut quadrature is intended for the locally integrable exponents
specified in the article; it is not a meromorphic-continuation algorithm.
"""
from __future__ import annotations
import mpmath as mp


def g(p):
    return mp.pi / mp.sin(mp.pi*p)


def weight(R,t):
    return (mp.pi/mp.cosh(mp.pi*t))**R/(2*mp.pi)


def realquad(fun):
    return mp.quad(fun,[-mp.inf,-1,0,1,mp.inf])


def master(R,orders,shifts,c=None):
    if len(orders)!=len(shifts) or not orders:
        raise ValueError('orders and shifts must have the same positive length')
    amin=min(mp.re(a) for a in shifts)
    if amin<=0 or mp.re(R)<=0:
        raise ValueError('positive real parts of shifts and depth are required')
    if c is None:
        c=(1+max(mp.mpf('0.5'),1-amin))/2
    if not max(0,1-amin)<c<1:
        raise ValueError('contour is not to the right of every branch point')
    return realquad(lambda t:g(c+1j*t)**R*mp.fprod(
        (c+1j*t+a-1)**(-s) for s,a in zip(orders,shifts)))/(2*mp.pi)


def central(R,orders,shifts):
    if any(a==mp.mpf('.5') for a in shifts):
        raise ValueError('central poles require the distributional convention')
    return realquad(lambda t:weight(R,t)*mp.fprod(
        (a-mp.mpf('.5')+1j*t)**(-s) for s,a in zip(orders,shifts)))


def cut_intervals(shifts):
    points=sorted(set([mp.mpf('.5')]+[1-a for a in shifts if a<mp.mpf('.5')]))
    return list(zip(points[:-1],points[1:]))


def cut(R,orders,shifts):
    total=mp.mpc(0)
    for left,right in cut_intervals(shifts):
        midpoint=(left+right)/2
        active=[midpoint<1-a for a in shifts]
        sigma=sum(s for s,flag in zip(orders,active) if flag)
        if not sigma: # sin(pi*sigma) can be zero without the continuation being zero!
            continue
        def f(x):
            return g(x)**R*mp.sin(mp.pi*sigma)/mp.pi*mp.fprod(
                abs(x+a-1)**(-s) for s,a in zip(orders,shifts))
        total+=mp.quad(f,[left,(left+right)/2,right])
    return total


def raw_logs(R,powers,shifts,c=mp.mpf('.5')):
    if c==mp.mpf('.5'):
        return realquad(lambda t:weight(R,t)*mp.fprod(
            mp.log(a-c+1j*t)**q if q else 1 for q,a in zip(powers,shifts)))
    return realquad(lambda t:g(c+1j*t)**R/(2*mp.pi)*mp.fprod(
        mp.log(c+a-1+1j*t)**q if q else 1 for q,a in zip(powers,shifts)))


def log_correction(R,powers,shifts):
    total=mp.mpc(0)
    for left,right in cut_intervals(shifts):
        active=[(left+right)/2<1-a for a in shifts]
        def f(x):
            lp=[mp.log(abs(x+a-1)) for a in shifts]
            upper=mp.fprod((l+1j*mp.pi*flag)**q for l,flag,q in zip(lp,active,powers))
            lower=mp.fprod((l-1j*mp.pi*flag)**q for l,flag,q in zip(lp,active,powers))
            return g(x)**R*(upper-lower)/(2j*mp.pi)
        total+=mp.quad(f,[left,(left+right)/2,right])
    return total


def completed_logs(R,powers,shifts):
    return raw_logs(R,powers,shifts)-log_correction(R,powers,shifts)


def bell_values(ds):
    b=[mp.mpf(1)]
    for n in range(1,len(ds)+1):
        b.append(sum(mp.binomial(n-1,k-1)*ds[k-1]*b[n-k] for k in range(1,n+1)))
    return b


def resonance_cumulants(n,q,odd=True,L=None):
    L=mp.log(2*mp.pi) if L is None else L
    ds=[]
    for k in range(1,q+1):
        H=sum(mp.mpf(j)**(-k) for j in range(1,n+1))
        if k==1:
            ds.append(L+mp.euler-H)
        else:
            correction=(mp.mpf(2)**(1-k) if odd else 2*(1-mp.mpf(2)**(-k))) if k%2==0 else 0
            ds.append(mp.factorial(k-1)*((1-correction)*mp.zeta(k)+(-1)**k*H))
    return ds


def z_classical(R,s):
    if R==1:
        return mp.mpf(2)**(-s)*(mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))
    if R==2:
        return mp.altzeta(s-1)
    raise ValueError('only depths 1 and 2 have been programmed for this independent check')


def centered_jet(R,w,q):
    # Differentiation of the original right contour, not of the reflected formula.
    c=mp.mpf('.75')
    return realquad(lambda t:g(c+1j*t)**R*(c-mp.mpf('.5')+1j*t)**(-w)*
                    (-mp.log(c-mp.mpf('.5')+1j*t))**q)/(2*mp.pi)


def reflected_jet(R,w,q):
    n=w-1
    odd=w%2==1
    bs=bell_values(resonance_cumulants(n,q,odd))
    if odd:
        m=(w-1)//2
        pref=(-1)**m*mp.pi*(2*mp.pi)**(R+2*m-1)/mp.factorial(2*m)
        return pref*sum(mp.binomial(q,j)*bs[q-j]*(-1)**j*
                        z_derivative(R,-n,j) for j in range(q+1))
    m=w//2
    pref=2*(-1)**(m+1)*(2*mp.pi)**(R+2*m-2)/mp.factorial(n)
    return pref*sum(mp.binomial(q,j)*bs[q-j]*(-1)**j*
                    z_derivative(R,-n,j+1)/(j+1) for j in range(q+1))


def z_derivative(R,s,j):
    # Tiny-step Hurwitz evaluation at s=0 can lose accuracy internally.
    # Cauchy differentiation avoids that special-case cancellation.
    if j==0: return z_classical(R,s)
    if R==1 and s==0:
        return mp.diff(lambda u:z_classical(R,u),s,j,method='quad',radius=mp.mpf('.15'))
    return mp.diff(lambda u:z_classical(R,u),s,j)


def complex_cut_segments(shifts):
    points=[1-a for a in shifts]
    ys=sorted(set(mp.im(p) for p in points))
    segments=[]
    for y in ys:
        group=[j for j,p in enumerate(points) if mp.im(p)==y]
        xs=sorted(set([mp.mpf('.5')]+[mp.re(points[j]) for j in group if mp.re(points[j])>mp.mpf('.5')]))
        for left,right in zip(xs[:-1],xs[1:]):
            active=[j for j in group if mp.re(points[j])>(left+right)/2]
            segments.append((y,left,right,group,active))
    return points,segments


def central_complex(R,orders,shifts,log_powers=None):
    breaks=sorted(set([-mp.inf,-1,0,1,mp.inf]+[mp.im(1-a) for a in shifts]))
    def f(t):
        zs=[a-mp.mpf('.5')+1j*t for a in shifts]
        vals=[z**(-s) for z,s in zip(zs,orders)] if log_powers is None else [mp.log(z)**q if q else 1 for z,q in zip(zs,log_powers)]
        return weight(R,t)*mp.fprod(vals)
    return mp.quad(f,breaks)


def cut_complex(R,orders,shifts,log_powers=None):
    points,segments=complex_cut_segments(shifts);total=mp.mpc(0)
    for y,left,right,group,active in segments:
        sigma=sum(orders[j] for j in active)
        def f(x):
            p=x+1j*y
            if log_powers is None:
                vals=[abs(x-mp.re(v))**(-s) if j in group else (p-v)**(-s) for j,(v,s) in enumerate(zip(points,orders))]
                return g(p)**R*mp.sin(mp.pi*sigma)/mp.pi*mp.fprod(vals)
            lp=[];lm=[]
            for j,v in enumerate(points):
                if j in active:
                    l=mp.log(abs(x-mp.re(v)));lp.append(l+1j*mp.pi);lm.append(l-1j*mp.pi)
                else:
                    l=mp.log(p-v);lp.append(l);lm.append(l)
            jump=(mp.fprod(l**q if q else 1 for l,q in zip(lp,log_powers))-
                  mp.fprod(l**q if q else 1 for l,q in zip(lm,log_powers)))/(2j)
            return g(p)**R*jump/mp.pi
        total+=mp.quad(f,[left,(left+right)/2,right])
    return total
