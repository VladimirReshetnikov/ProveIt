#!/usr/bin/env python3
"""Finite audits for Interior Root Collisions in Catalan Hankel Determinants.

Exact tests use fractions.Fraction only. Numerical tests require mpmath.
The tests are reproducible checks, not proofs or interval certificates.
Run: python code/verify.py --out data
"""
from __future__ import annotations
import argparse, csv, itertools, json, math, platform, time
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence
import mpmath as mp


def determinant(a):
    """Gaussian elimination; exact for Fraction input, high precision for mp input."""
    n = len(a)
    if not n:
        return Q(1)
    b = [list(row) for row in a]
    ans = b[0][0] * 0 + 1
    for j in range(n):
        pivot = next((i for i in range(j, n) if b[i][j] != 0), None)
        if pivot is None:
            return ans * 0
        if pivot != j:
            b[j], b[pivot] = b[pivot], b[j]
            ans = -ans
        p = b[j][j]
        ans *= p
        for i in range(j + 1, n):
            factor = b[i][j] / p
            for k in range(j + 1, n):
                b[i][k] -= factor * b[j][k]
    return ans


def poly_product_roots(roots):
    a = [Q(1)]
    for c in roots:
        b = [a[0] * 0] * (len(a) + 1)
        for j, v in enumerate(a):
            b[j] -= c * v
            b[j + 1] += v
        a = b
    return a


def catalan(n: int) -> int:
    return math.comb(2*n, n) // (n + 1)


def moment_hankel(n: int, roots):
    q = poly_product_roots(roots)
    return determinant([[sum(q[r] * catalan(i+j+r) for r in range(len(q)))
                         for j in range(n)] for i in range(n)])


def groups(values):
    out = []
    for v in values:
        for j, (u, m) in enumerate(out):
            if v == u:
                out[j] = (u, m + 1)
                break
        else:
            out.append((v, 1))
    return out


def christoffel(n: int, roots):
    """Confluent Christoffel formula, evaluated by polynomial Taylor jets."""
    d = len(roots)
    if not d:
        return roots[0] * 0 + 1 if roots else Q(1)
    gs = groups(roots)
    rows = []
    den = roots[0] * 0 + 1
    for a, (c, m) in enumerate(gs):
        zero = c * 0
        prev = [zero] * m
        cur = [zero + 1] + [zero] * (m - 1)
        jets = []
        for ell in range(n + d):
            if ell >= n:
                jets.append(cur[:])
            shift = c - (1 if ell == 0 else 2)
            nxt = [shift * cur[r] - prev[r] + (cur[r-1] if r else 0)
                   for r in range(m)]
            prev, cur = cur, nxt
        rows += [[jets[j][r] for j in range(d)] for r in range(m)]
        for c2, m2 in gs[a+1:]:
            den *= (c2-c) ** (m*m2)
    return (-1)**(n*d) * determinant(rows) / den


def vandermonde(v):
    return mp.fprod(v[j]-v[i] for i in range(len(v)) for j in range(i+1,len(v)))


def S0(d: int, k: int):
    r = d-k
    return Q(2**(k*r) * math.prod(math.factorial(j) for j in range(k))
             * math.prod(math.factorial(j) for j in range(r)),
             math.prod(math.factorial(j) for j in range(d)))


def mq(q):
    return mp.mpf(q.numerator) / q.denominator if isinstance(q,Q) else mp.mpf(q)


def profile_S(u, k: int):
    """Entire profile S_{d,k}, including exact repeated coordinates."""
    d = len(u)
    if not 0 <= k <= d:
        raise ValueError('k must lie in [0,d]')
    gs = groups(u)
    rows = []
    den = mp.mpc(1)
    columns = [(1,j) for j in range(k)] + [(-1,j) for j in range(d-k)]
    for a,(v,m) in enumerate(gs):
        for r in range(m):
            rows.append([mp.exp(s*v)*sum(math.comb(j,l)*v**(j-l)*s**(r-l)
                         /mp.factorial(r-l) for l in range(min(r,j)+1))
                         for s,j in columns])
        for v2,m2 in gs[a+1:]:
            den *= (v2-v)**(m*m2)
    return (-1)**(k*(d-k))*determinant(rows)/den


def coefficient_C(d: int,k: int,w):
    r=d-k
    e=k*(k-1)//2+r*(r-1)//2
    return (-1)**(r*(r+1)//2)/( (2*mp.sinh(w/2))**d * (2*mp.sinh(w))**e )


def shc(x):
    return mp.sinh(x)/x if x else mp.mpf(1)


def sector_F(h,u,k,w):
    """Analytic sector amplitude by confluent determinant and exact-degree DFT.
    DFT is high-precision arithmetic, not an interval enclosure.
    """
    d=len(u); r=d-k; e=k*(k-1)//2+r*(r-1)//2
    gs=groups(u)
    alphas=[mp.mpf(j)-mp.mpf(d-1)/2 for j in range(d)]
    cross=mp.mpc(1)
    for a,(v,m) in enumerate(gs):
        for v2,m2 in gs[a+1:]:
            cross *= (v2-v)**(m*m2)
    vals=[]
    for ell in range(d+1):
        t=mp.exp(2j*mp.pi*ell/(d+1))
        mat=[]
        for v,m in gs:
            for rr in range(m):
                mat.append([(t*mp.exp(v+alpha*(w+h*v))*(1+alpha*h)**rr
                             -mp.exp(-v-alpha*(w+h*v))*(-1-alpha*h)**rr)
                            /mp.factorial(rr) for alpha in alphas])
        vals.append(determinant(mat)*t**(-k))
    coeff=sum(vals)/(d+1)/cross/h**e
    den=mp.fprod(2*mp.sinh((w+h*v)/2) for v in u)
    den*=mp.fprod(2*mp.sinh(w+h*(u[i]+u[j])/2)*shc(h*(u[j]-u[i])/2)
                  for i in range(d) for j in range(i+1,d))
    return coeff/den


def first_coefficient(u,k,w):
    d=len(u); kr=k*(d-k)
    S=profile_S(u,k)
    E=mp.diff(lambda a:profile_S([a*v for v in u],k),mp.mpf(1))
    A=mp.coth(w/2)/2+(d-2)*mp.coth(w)/4
    B=(2*k-d)*mp.coth(w)/4
    return coefficient_C(d,k,w)*(-A*sum(u)*S-B*(E+kr*S))


def collision_hankel(n,t,theta,tau):
    nu=mp.mpf(n+t)
    roots=[2+2*mp.cos(theta+tau/nu)]*t+[2+2*mp.cos(theta-tau/nu)]*t
    return christoffel(n,roots)


def A_normalization(t,theta):
    return mq(S0(2*t,t))/((2*mp.sin(theta/2))**(2*t)
                          *(2*mp.sin(theta))**(t*(t-1)))


def jacobi_moments(t,tau):
    omega=2*tau
    if not omega:
        return [mp.mpf(1)/(j+1) if j%2==0 else mp.mpf(0) for j in range(2*t-1)]
    if abs(omega)<1:
        out=[]
        for j in range(2*t-1):
            val=mp.mpc(0); term=mp.mpc(1)
            for ell in range(500):
                if (j+ell)%2==0:
                    val+=term/(j+ell+1)
                term*=1j*omega/(ell+1)
                if ell>30 and abs(term)<mp.eps**mp.mpf('.9'):
                    break
            out.append(val)
        return out
    v=[mp.sin(omega)/omega]
    for j in range(1,2*t-1):
        v.append((mp.exp(1j*omega)-(-1)**j*mp.exp(-1j*omega))/(2j*omega)
                 -j/(1j*omega)*v[-1])
    return v


def Phi(t,tau):
    m=jacobi_moments(t,tau); m0=jacobi_moments(t,0)
    return determinant([[m[i+j] for j in range(t)] for i in range(t)])/determinant(
           [[m0[i+j] for j in range(t)] for i in range(t)])


def Psi(t,tau):
    return profile_S([1j*tau]*t+[-1j*tau]*t,t+1)/mq(S0(2*t,t))


def padd(a,b):
    c=dict(a)
    for key,v in b.items():
        c[key]=c.get(key,Q(0))+v
        if not c[key]: del c[key]
    return c


def pmul(a,b,H):
    c={}
    for (j,l),v in a.items():
        for (j2,l2),v2 in b.items():
            if l+l2<=H:
                key=(j+j2,l+l2)
                c[key]=c.get(key,Q(0))+v*v2
    return {k:v for k,v in c.items() if v}


def exact_collision_polynomial(d, q=Q(2)):
    """Coefficient of det of normalized u-jets at u=0, as Q[t,h]."""
    H=d*(d-1)//2+1
    entries=[]
    for r in range(d):
        row=[]
        for j in range(d):
            alpha=Q(2*j-d+1,2)
            a={}
            for ell in range(r+1):
                f=Q(math.comb(r,ell),math.factorial(r))*alpha**ell
                if f:
                    a[(1,ell)]=f*q**(2*j-d+1)
                    a[(0,ell)]=-(-1)**r*f*q**(-2*j+d-1)
            row.append(a)
        entries.append(row)
    dp={0:{(0,0):Q(1)}}
    for r in range(d):
        nd={}
        for mask,poly in dp.items():
            for j in range(d):
                if mask>>j&1:continue
                inv=(mask>>(j+1)).bit_count()
                term=pmul(poly,entries[r][j],H)
                if inv%2:term={k:-v for k,v in term.items()}
                m=mask|1<<j
                nd[m]=padd(nd.get(m,{}),term)
        dp=nd
    return dp[(1<<d)-1]


def run(out: Path):
    out.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=100
    counts={}; metrics={}; start=time.time()
    def exact(name,cond):
        if not cond:raise AssertionError(name)
        counts[name]=counts.get(name,0)+1
    maxerrs={}
    def near(name,a,b,tol=mp.mpf('1e-65')):
        err=abs(a-b)/(1+abs(a)+abs(b))
        if err>tol:raise AssertionError(f'{name}: {mp.nstr(err,8)}')
        counts[name]=counts.get(name,0)+1
        maxerrs[name]=max(maxerrs.get(name,mp.mpf(0)),err)
    # Exact moment / confluent orthogonal-polynomial identity.
    rootsets=[[],[Q(0)],[Q(1)],[Q(2),Q(2)],[Q(1),Q(3)],
              [Q(-1),Q(2),Q(2)],[Q(1),Q(1),Q(3),Q(3)],
              [Q(0)]*3+[Q(4)]*2,[Q(1,2)]*2+[Q(7,2)]*3]
    for n in range(7):
        for roots in rootsets:
            exact('moment_Christoffel',moment_hankel(n,roots)==christoffel(n,roots))
    # Exact centered exponential Vandermonde at e^{v_i}=r_i^2.
    for d in range(1,8):
        rr=[Q(i+2,i+1) for i in range(d)]
        left=determinant([[r**(2*j-d+1) for j in range(d)] for r in rr])
        right=math.prod(rr[j]/rr[i]-rr[i]/rr[j]
                        for i in range(d) for j in range(i+1,d))
        exact('centered_Vandermonde',left==right)
    # Exact all-collided sector valuations and first Taylor coefficients.
    for d in range(1,8):
        p=exact_collision_polynomial(d)
        z=Q(4); B=z-1/z; cot=(z+1/z)/(z-1/z)
        for k in range(d+1):
            r=d-k; e=k*(k-1)//2+r*(r-1)//2
            for ell in range(e):
                exact('sector_forced_zeros',p.get((k,ell),Q(0))==0)
            v=(-1)**(r*(r+1)//2)*B**(k*r)*S0(d,k)
            exact('sector_leading_coefficient',p.get((k,e),Q(0))==v)
            v1=-v*Q((2*k-d)*k*r,4)*cot
            exact('sector_first_coefficient',p.get((k,e+1),Q(0))==v1)
    # Entire profile values and Jacobi/Hankel duality, including collision at 0.
    for d in range(1,8):
        for k in range(d+1):
            near('profile_origin',profile_S([mp.mpf(0)]*d,k),mq(S0(d,k)))
    for t in range(1,6):
        for tau in [mp.mpf(0),mp.mpf('.17'),mp.mpf('.8'),mp.mpf('2.3'),mp.mpc('.4','.2')]:
            near('profile_Jacobi_duality',profile_S([1j*tau]*t+[-1j*tau]*t,t)
                 /mq(S0(2*t,t)),Phi(t,tau))
    # Exact sector decomposition at finite inverse size and collided coordinates.
    for d in range(1,6):
        for w in [mp.mpf('.7'),mp.mpc('.2','.9'),mp.mpc(0,'1.1')]:
            for u in [[mp.mpf(j)/7 for j in range(d)],[mp.mpf(0)]*d]:
                n=7;nu=mp.mpf(n)+mp.mpf(d)/2;h=1/nu
                roots=[2+2*mp.cosh(w+h*v) for v in u]
                total=sum(mp.exp((2*k-d)*nu*w)*nu**(k*(d-k))*sector_F(h,u,k,w)
                          for k in range(d+1))*(-1)**(n*d)
                near('finite_sector_identity',total,christoffel(n,roots),mp.mpf('1e-60'))
    # First correction independently via numerical analytic derivatives.
    h=mp.mpf('0.000001');w=mp.mpc('.3','.8')
    scaled=[]
    for d in range(1,5):
        u=[mp.mpf(j-1)/5 for j in range(d)]
        for k in range(d+1):
            a0=coefficient_C(d,k,w)*profile_S(u,k)
            a1=first_coefficient(u,k,w)
            # Symmetric derivative suppresses quadratic error.
            num=(sector_F(h,u,k,w)-sector_F(-h,u,k,w))/(2*h)
            near('first_correction_numeric',num,a1,mp.mpf('1e-10'))
            scaled.append(float(abs(sector_F(h,u,k,w)-a0-h*a1)/h**2/(1+abs(a0))))
    metrics['max_scaled_second_order_amplitude_residual']=max(scaled)
    # Pairing/Gram formula at distinct coordinates and paired confluence.
    for m in range(1,5):
        x=[mp.mpf(j*j)/7 for j in range(m)]
        y=[mp.mpf(j+1)/9 for j in range(m)]
        sinc=lambda v:mp.sin(v)/v if v else mp.mpf(1)
        rhs=2**m*determinant([[sinc(a-b) for b in y] for a in x])/(vandermonde(x)*vandermonde(y))
        near('bilinear_sine_kernel',profile_S([1j*a for a in x+y],m),rhs)
    # Multiple separated clusters: check leading product and convergence.
    multi=[]
    ws=[mp.mpc(0,'.8'),mp.mpc(0,'1.7')]; ds=[2,2]; ks=[1,1]
    us=[[mp.mpf('.2'),mp.mpf('-.1')],[mp.mpf('.3'),mp.mpf('.05')]]
    lead=mp.mpc(1)
    for dd,kk,ww,uu in zip(ds,ks,ws,us):lead*=coefficient_C(dd,kk,ww)*profile_S(uu,kk)
    ca,cb=[2+2*mp.cosh(ww) for ww in ws]
    for sa in [1,-1]:
        for sb in [1,-1]:lead*=2*mp.sinh((sb*ws[1]-sa*ws[0])/2)
    lead/=(cb-ca)**4
    for n in [40,80,160,320]:
        nu=mp.mpf(n+2)
        roots=[2+2*mp.cosh(ww+v/nu) for ww,uu in zip(ws,us) for v in uu]
        val=christoffel(n,roots)/nu**2
        multi.append({'N':n,'absolute_error':float(abs(val-lead)),
                      'nu_times_error':float(nu*abs(val-lead))})
    metrics['multi_cluster_checks']=multi
    # Explicit two-root formula, including exact tau=0 by continuity.
    theta=mp.mpf('1.1')
    for n in [3,12,47]:
        nu=mp.mpf(n+1)
        for tau in [mp.mpf(0),mp.mpf('.2'),mp.pi/2,mp.mpf('2.4')]:
            first=2*nu if not tau else mp.sin(2*tau)/mp.sin(tau/nu)
            rhs=(first-mp.sin(2*nu*theta)/mp.sin(theta))/(4*mp.sin((theta+tau/nu)/2)*mp.sin((theta-tau/nu)/2))
            near('two_simple_roots_exact_formula',collision_hankel(n,1,theta,tau),rhs)
    # Finite-size correction and zero transport.
    correction_rows=[];zero_rows=[]
    for t in [1,2,3]:
        tau=mp.mpf('.8')
        phi=Phi(t,tau);psi=Psi(t,tau)
        for n in [40,80,160,320]:
            nu=mp.mpf(n+t)
            val=collision_hankel(n,t,theta,tau)/(A_normalization(t,theta)*nu**(t*t))
            first=(-1)**t*mp.sin(2*nu*theta)/mp.sin(theta)*psi/nu
            correction_rows.append({'t':t,'N':n,'absolute_error_leading':float(abs(val-phi)),
               'absolute_error_corrected':float(abs(val-phi-first)),
               'scaled_corrected_error':float(abs(val-phi-first)*nu**2)})
    for t,guess in [(1,mp.pi/2),(3,2*mp.pi-mp.mpf('.08'))]:
        root=mp.findroot(lambda s:mp.re(Phi(t,s)),(guess-mp.mpf('.1'),guess+mp.mpf('.1')))
        der=mp.diff(lambda s:Phi(t,s),root)
        psi=Psi(t,root)
        for n in [40,80,160,320]:
            nu=mp.mpf(n+t)
            shift=(-1)**(t+1)*mp.sin(2*nu*theta)/mp.sin(theta)*psi/(nu*der)
            fn=lambda s:mp.re(collision_hankel(n,t,theta,s)/(A_normalization(t,theta)*nu**(t*t)))
            rn=mp.findroot(fn,(root+mp.re(shift)-mp.mpf('.01'),root+mp.re(shift)+mp.mpf('.01')))
            zero_rows.append({'t':t,'N':n,'profile_zero':mp.nstr(root,25),
               'finite_N_zero':mp.nstr(rn,25),'predicted_shift':mp.nstr(mp.re(shift),18),
               'scaled_shift_error':float(abs(rn-root-shift)*nu**2)})
    # Classical Jacobi Fourier parity/asymptotic audit, explicitly not new claims.
    parity=[]
    for t in [1,2,3,4,5]:
        Z=mp.mpf(2)**(t*t)*mp.fprod(mp.factorial(j)**2*mp.factorial(j+1)/mp.factorial(t+j)
                                  for j in range(t))
        L=lambda m:mp.fprod(mp.factorial(j)*mp.factorial(j-1) for j in range(1,m+1))
        m=t//2
        for s in [mp.mpf('12.3'),mp.mpf('24.3'),mp.mpf('48.3')]:
            if t%2:
                E=(t*t+1)//2;B=math.comb(t,m)*L(m)*L(m+1)/Z
                norm=Phi(t,s)*s**E/((-1)**m*B)
                leading=mp.sin(2*s)+mp.mpf(m*(m+1))/(2*s)*mp.cos(2*s)
                err=float(abs(norm-leading)*s*s)
            else:
                E=t*t//2;B=math.comb(t,m)*L(m)**2/Z
                norm=Phi(t,s)*s**E/B
                err=float(abs(norm-1)*s*s)
                exact('even_profile_positive_sample',mp.re(Phi(t,s))>0)
            parity.append({'t':t,'s':float(s),'scaled_residual':err})
    for name,rows in [('finite_size_corrections.csv',correction_rows),('zero_transport.csv',zero_rows),
                      ('jacobi_parity_audit.csv',parity),('multiple_clusters.csv',multi)]:
        with (out/name).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    result={'python':platform.python_version(),'mpmath':mp.__version__,'precision_decimal_digits':mp.mp.dps,
            'status':'all assertions passed; not a proof-assistant or interval certificate',
            'assertion_counts':counts,'total_assertions':sum(counts.values()),
            'maximum_relative_discrepancies':{k:mp.nstr(v,12) for k,v in maxerrs.items()},
            'metrics':metrics,'elapsed_seconds':round(time.time()-start,3)}
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('data'))
    run(parser.parse_args().out)
