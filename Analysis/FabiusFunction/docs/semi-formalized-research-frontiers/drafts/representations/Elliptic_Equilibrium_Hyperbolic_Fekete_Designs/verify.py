#!/usr/bin/env python3
"""Reproducible checks for Elliptic Equilibrium and Boundary-Corrected Transseries.
Numerical diagnostics are not interval certificates or substitutes for the proofs.
Requires Python 3.10+, numpy, scipy, mpmath, sympy; matplotlib for --figures.
"""
from __future__ import annotations
import argparse, csv, json, platform
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import solve
from scipy.special import ellipk
from scipy.integrate import quad
import mpmath as mp
import sympy as sy


def kernel(x: np.ndarray | float) -> np.ndarray:
    q = np.exp(-2 * np.asarray(x))
    return np.log1p(q) - np.log1p(-q)


def energy_derivatives(u: np.ndarray):
    diff = u[:, None] - u[None, :]
    dist = np.abs(diff)
    np.fill_diagonal(dist, np.inf)
    q = np.exp(-2 * dist)
    value = np.sum(np.triu(np.log1p(q) - np.log1p(-q), 1))
    vp = -4*q/(1-q*q)
    vpp = 8*q*(1+q*q)/(1-q*q)**2
    gradient = np.sum(np.sign(diff)*vp, axis=1)
    hessian = np.diag(vpp.sum(axis=1)) - vpp
    return value, gradient[1:-1], hessian[1:-1, 1:-1]


def optimize(n: int, L: float):
    if n < 2 or L <= 0:
        raise ValueError('n must be >=2 and L must be positive')
    u = np.linspace(0, L, n)
    for it in range(100):
        E, g, H = energy_derivatives(u)
        if not len(g):
            return u, float(E), 0.0
        step = solve(H, -g, assume_a='pos')
        if np.max(np.abs(step)) < 2e-13 * max(1., L):
            return u, float(E), float(np.max(np.abs(g)))
        alpha = 1.
        for _ in range(60):
            trial = u.copy()
            trial[1:-1] += alpha*step
            if np.all(np.diff(trial)>0):
                Enew = energy_derivatives(trial)[0]
                if Enew <= E + 1e-4*alpha*np.dot(g, step) + 1e-14*max(1.,E):
                    u = trial
                    break
            alpha *= .5
        else:
            raise ArithmeticError('Newton line search failed')
    raise ArithmeticError('Newton iteration did not converge')


def optimize_mp(n: int, h):
    h = mp.mpf(h)
    u = mp.matrix([i*h for i in range(n)])
    for _ in range(40):
        g = mp.matrix(n-2, 1); H = mp.matrix(n-2)
        for i in range(1,n-1):
            for j in range(n):
                if i==j: continue
                x=abs(u[i]-u[j]); q=mp.exp(-2*x)
                vp=-4*q/(1-q*q); vpp=8*q*(1+q*q)/(1-q*q)**2
                g[i-1] += mp.sign(u[i]-u[j])*vp
                H[i-1,i-1] += vpp
                if 0<j<n-1: H[i-1,j-1] -= vpp
        step=mp.lu_solve(H,-g)
        for i in range(n-2): u[i+1] += step[i]
        if max(abs(x) for x in step)<mp.mpf('1e-65'): break
    E=mp.fsum(mp.log1p(mp.exp(-2*(u[j]-u[i])))-mp.log1p(-mp.exp(-2*(u[j]-u[i])))
              for i in range(n) for j in range(i+1,n))
    return u,E


def mpV(x):
    q=mp.exp(-2*x)
    return mp.log1p(q)-mp.log1p(-q)


def equilibrium_checks():
    out=[]
    for Lstr in ['0.2','1','3']:
        L=mp.mpf(Lstr); b=mp.exp(2*L); K=mp.ellipk(1-b**-2)
        I=mp.pi*mp.ellipk(b**-2)/K
        def t(th): return mp.sqrt(1+(b*b-1)*mp.sin(th)**2)
        def w(th): return b/(K*t(th))
        norm=mp.quad(w,[0,mp.pi/2])
        for f in ['0.1','0.5','0.9']:
            v=L*mp.mpf(f); tv=mp.exp(2*v)
            split=mp.asin(mp.sqrt((tv*tv-1)/(b*b-1)))
            def integrand(th):
                ts=t(th)
                # log singularity is integrable; quadrature nodes are interior.
                return w(th)*mp.log(abs((tv+ts)/(tv-ts)))
            pot=mp.quad(integrand,[0,split,mp.pi/2])
            out.append(dict(L=Lstr, fraction=f, energy=mp.nstr(I,30),
                            normalization_error=mp.nstr(abs(norm-1),5),
                            potential_error=mp.nstr(abs(pot-I),5)))
            assert abs(norm-1)<mp.mpf('1e-65')
            assert abs(pot-I)<mp.mpf('1e-60')
    return out


def product_checks():
    out=[]
    for hstr in ['0.2','0.5','1','2']:
        h=mp.mpf(hstr); q=mp.exp(-2*h); Q=mp.exp(-mp.pi**2/h)
        S=mp.log(mp.qp(q*q))-2*mp.log(mp.qp(q))
        modular=mp.pi**2/(8*h)+mp.log(h/(2*mp.pi))/2 +mp.log(mp.qp(Q))-2*mp.log(mp.qp(Q*Q))
        assert abs(S-modular)<mp.mpf('1e-65')
        n=9
        T=mp.fsum(k*mpV(k*h) for k in range(1,1400))
        U=mp.fsum((n-k)*mpV(k*h) for k in range(1,n))
        R=mp.fsum(2*q**(r*(n+1))/(r*(1-q**r)**2) for r in range(1,1000,2))
        assert abs(U-(n*S-T+R))<mp.mpf('1e-60')
        out.append(dict(h=hstr, S=mp.nstr(S,30), modular_error=mp.nstr(abs(S-modular),5),
                        finite_factorization_error=mp.nstr(abs(U-(n*S-T+R)),5)))
    return out


def symbolic_checks():
    z=sy.symbols('z'); H=sy.symbols('H')
    a=[sy.rf(sy.Rational(1,2),j)**2/sy.factorial(j)**2 for j in range(7)]
    A=sum(a[j]*z**j for j in range(7))
    D=sum(a[j]*2*(sy.harmonic(2*j)-sy.harmonic(j))*z**j for j in range(1,7))
    B=sy.series(D/A,z,0,7)
    assert B.removeO().coeff(z,1)==sy.Rational(1,4)
    assert B.removeO().coeff(z,2)==sy.Rational(13,128)
    eps,a0=sy.symbols('eps a')
    n=1/eps; q=a0*eps
    U=2*(n-1)*q+2*(n-2)*q**2+(sy.Rational(8,3)*n-sy.Rational(20,3))*q**3+(2*n-8)*q**4
    E=sy.series(U-2*(n-3)/(n-1)*q**3,eps,0,4).removeO().expand()
    expected=2*a0+(2*a0**2-2*a0)*eps+(sy.Rational(8,3)*a0**3-4*a0**2)*eps**2+(2*a0**4-sy.Rational(26,3)*a0**3)*eps**3
    assert sy.expand(E-expected)==0
    c=[]
    for j in range(1,9):
        c.append(sy.simplify((-sy.divisor_sigma(j)+(4*sy.divisor_sigma(j//2) if j%2==0 else 0))/j))
    inverse=[]
    for j in range(1,7):
        coeff=sy.series(sy.diff(B.removeO(),z)*sy.exp(-2*j*B.removeO()),z,0,j).removeO().coeff(z,j-1)/(2*j)
        inverse.append(sy.simplify(coeff*16**j))
    assert inverse == [sy.Integer(2),sy.Integer(-3),sy.Rational(8,3),sy.Rational(-3,2),sy.Rational(12,5),sy.Integer(-4)]
    return dict(B_series=str(B), critical_series=str(E), modular_coefficients=list(map(str,c)),
                inverse_capacity_coefficients=list(map(str,inverse)))


def run(outdir: Path, figures: bool=False):
    outdir.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=80
    results={'environment':dict(python=platform.python_version(), numpy=np.__version__,
                               scipy=scipy.__version__,mpmath=mp.__version__,sympy=sy.__version__),
             'symbolic':symbolic_checks(), 'equilibrium':equilibrium_checks(),
             'products':product_checks()}
    boundary=[]
    for n in [4,8,16]:
        for h in [2,3,4]:
            u,E=optimize_mp(n,h); q=mp.exp(-2*h)
            U=mp.fsum((n-k)*mpV(k*h) for k in range(1,n))
            pred=mp.mpf(2)*(n-3)/(n-1)
            gain=(U-E)/q**3
            e=mp.matrix([1 if i in [0,n-2] else 0 for i in range(n-1)])
            err=mp.sqrt(mp.fsum(((u[i+1]-u[i]-h)+q*(e[i]-mp.mpf(2)/(n-1))/2)**2 for i in range(n-1)))
            boundary.append(dict(n=n,h=h,gain_over_q3=mp.nstr(gain,20),limit=mp.nstr(pred,20),
                                 energy_error_over_q4=mp.nstr((U-E-pred*q**3)/q**4,14),
                                 gap_error_over_q2=mp.nstr(err/q**2,14)))
    results['boundary']=boundary
    inversion=[]
    for L in [1,2,3]:
        L=mp.mpf(L); z=mp.exp(-4*L)
        I=mp.pi*mp.ellipk(z)/mp.ellipk(1-z)
        Q=mp.exp(-mp.pi**2/I)
        inverse=mp.pi**2/(4*I)-mp.log(2)+2*Q-3*Q**2+mp.mpf(8)/3*Q**3-mp.mpf(3)/2*Q**4+mp.mpf(12)/5*Q**5
        # The omitted sixth coefficient is -4.
        inversion.append(dict(L=str(L),error_over_Q6=mp.nstr((L-inverse)/Q**6,20)))
    results['inverse_capacity']=inversion
    finite=[]; fixed=[]; critical=[]
    for n in [8,16,32,64,128]:
        u,E,gres=optimize(n,1.)
        I=float(mp.pi*mp.ellipk(mp.exp(-4))/mp.ellipk(1-mp.exp(-4)))
        fixed.append(dict(n=n,L=1.,normalized_energy=2*E/(n*(n-1)),limit=I,stationarity=gres))
        for h in [.5,1.,2.]:
            L=(n-1)*h; u,E,gres=optimize(n,L)
            k=np.arange(1,n); U=float(np.sum((n-k)*kernel(k*h)))
            B=float(np.sum((n-k)*kernel(k*L/(n-k))))
            assert B-1e-9<=E<=U+1e-9
            finite.append(dict(n=n,h=h,lower=B,optimal=E,upper=U,stationarity=gres))
        s=0.; h=.5*np.log(n)+s; u,E,gres=optimize(n,(n-1)*h)
        app=2.-4/(3*n*n)-20/(3*n**3)
        critical.append(dict(n=n,energy=E,determinant=np.exp(-2*E),
                             three_correction_energy=app,
                             residual_times_n4=(E-app)*n**4,stationarity=gres))
    results.update(fixed_interval=fixed,finite_certificates=finite,critical=critical)
    # ed. (ProveIt, 2026-09-29): newline='\n' here and lineterminator='\n' in the
    # CSV writer (csv defaults to CRLF) keep reruns LF on every platform.
    (outdir/'verification.json').write_text(json.dumps(results,indent=2)+'\n',newline='\n')
    for key in ['boundary','fixed_interval','finite_certificates','critical','equilibrium','products']:
        rows=results[key]
        with (outdir/(key+'.csv')).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys(),lineterminator='\n'); w.writeheader(); w.writerows(rows)
    if figures:
        import matplotlib
        matplotlib.use('Agg')
        # ed. (ProveIt, 2026-09-29): embed TrueType (Type 42) fonts instead of the
        # Type 3 fonts that Matplotlib writes by default.
        matplotlib.rcParams['pdf.fonttype']=42
        matplotlib.rcParams['ps.fonttype']=42
        import matplotlib.pyplot as plt
        x=np.linspace(.002,.998,1400)
        fig,ax=plt.subplots(figsize=(6.3,3.7))
        for L in [.1,1.,3.]:
            density=2*L/(ellipk(-np.expm1(-4*L))*np.sqrt(-np.expm1(-4*L*x)*-np.expm1(-4*L*(1-x))))
            ax.plot(x,density,label=f'L = {L:g}')
        ax.set(xlabel='Rescaled position u/L',ylabel='Rescaled density L ρ(Lx)',ylim=(.5,4.5))
        ax.legend(); fig.tight_layout();fig.savefig(outdir/'equilibrium_density.pdf');plt.close(fig)
        svalues=np.linspace(-.7,1.,30)
        fig,ax=plt.subplots(figsize=(6.3,3.7))
        for n in [8,32,96]:
            ys=[]
            for s in svalues:
                h=.5*np.log(n)+s
                _,E,_=optimize(n,(n-1)*h)
                ys.append(np.exp(-2*E))
            ax.plot(svalues,ys,label=f'n = {n}')
        ax.plot(svalues,np.exp(-4*np.exp(-2*svalues)),linestyle='--',label='Limit')
        ax.set(xlabel='Transition parameter s',ylabel='Optimal determinant')
        ax.legend();fig.tight_layout();fig.savefig(outdir/'determinant_transition.pdf');plt.close(fig)
    print(json.dumps(results,indent=2))
    print('All assertions passed. Numerical outputs are diagnostics, not interval certificates.')

if __name__=='__main__':
    # ed. (ProveIt, 2026-09-29): the default output is now a scratch directory
    # verification_rerun/ beside this script, and writing into the recorded
    # verification/ directory (whose floating-point values differ in their last
    # digits between platforms, and whose figures the article includes) needs the
    # explicit flag --overwrite-recorded. Standard output is written with LF so a
    # redirected log matches the recorded verification.log line endings.
    import sys
    sys.stdout.reconfigure(newline='\n')
    here=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=here/'verification_rerun')
    p.add_argument('--figures',action='store_true')
    p.add_argument('--overwrite-recorded',action='store_true',
                   help='allow writing into the recorded verification/ directory')
    args=p.parse_args()
    if args.output.resolve()==(here/'verification').resolve() and not args.overwrite_recorded:
        p.error('refusing to overwrite the recorded verification/ directory; '
                'pass --overwrite-recorded or choose another --output')
    run(args.output,args.figures)
