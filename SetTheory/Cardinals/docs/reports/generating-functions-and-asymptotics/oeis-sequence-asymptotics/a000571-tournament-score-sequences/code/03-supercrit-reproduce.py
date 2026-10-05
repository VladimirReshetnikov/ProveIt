#!/usr/bin/env python3
"""Reproduce the finite checks in Beyond Criticality.

Exact integer checks and floating asymptotic diagnostics are kept separate.
This program performs no network requests and writes only to --output.
The O(N^2) numerical recurrences use NumPy float64; constants/kernels use
mpmath. These calculations are diagnostics, NOT interval certificates.
"""
from __future__ import annotations
import argparse, csv, json, math, platform, sys, time
from itertools import combinations_with_replacement
from pathlib import Path
import mpmath as mp
import numpy as np


def divisors(n: int) -> list[int]:
    out = []
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
    return sorted(out)


def arithmetic_counts(N: int) -> tuple[list[int], list[int], list[int]]:
    phi = list(range(N + 1))
    for p in range(2, N + 1):
        if phi[p] == p:
            for j in range(p, N + 1, p):
                phi[j] -= phi[j] // p
    a, S, I = [0] * (N + 1), [0] * (N + 1), [0] * (N + 1)
    S[0] = 1
    for n in range(1, N + 1):
        numerator = sum((-1) ** (n + d) * phi[n // d] * math.comb(2*d, d)
                        for d in divisors(n))
        assert numerator % (2*n) == 0
        a[n] = numerator // (2*n)
        s = sum(a[k] * S[n-k] for k in range(1, n+1))
        b = a[n] - sum(a[k] * I[n-k] for k in range(1, n))
        assert s % n == b % n == 0
        S[n], I[n] = s // n, b // n
        assert S[n] >= 0 and I[n] >= 0
    return a, S, I


def exact_checks(a: list[int], S: list[int], I: list[int], max_brute: int = 10) -> dict:
    assert S[:14] == [1,1,1,2,4,9,22,59,167,490,1486,4639,14805,48107]
    assert I[:11] == [0,1,0,1,1,3,7,21,61,184,573]
    assert a[1:11] == [1,1,4,9,26,76,246,809,2704,9226]
    polys = [[0] * (max_brute+1) for _ in range(max_brute+1)]
    polys[0][0] = 1
    for n in range(1, max_brute+1):
        for k in range(1, n+1):
            polys[n][k] = sum(I[j]*polys[n-j][k-1] for j in range(1, n+1))
    brute = []
    for n in range(1, max_brute+1):
        counts = [0] * (max_brute+1)
        for s in combinations_with_replacement(range(n), n):
            if sum(s) != n*(n-1)//2:
                continue
            partial, blocks, valid = 0, 0, True
            for k, x in enumerate(s, 1):
                partial += x
                if partial < k*(k-1)//2:
                    valid = False
                    break
                blocks += partial == k*(k-1)//2
            if valid:
                counts[blocks] += 1
        assert counts == polys[n]
        assert sum(counts) == S[n]
        brute.append({'n': n, 'all': S[n], 'strong': I[n], 'by_blocks': counts[:n+1]})
    return {'oeis_initial_terms': 'PASS', 'integer_recurrences_through': len(S)-1,
            'landau_enumeration_and_component_polynomial_through': max_brute,
            'brute_enumeration': brute}


class Model:
    def __init__(self, arithmetic: list[int], dps: int = 60):
        mp.mp.dps = dps
        self.R = [mp.mpf(0)]
        for n in range(1, len(arithmetic)):
            # R_n * rho^n = (N_n - central_binomial/(2n))/(n*4^n).
            num = 2*n*arithmetic[n] - math.comb(2*n, n)
            self.R.append(mp.mpf(num) / (2*n*n*mp.mpf(4)**n))
        self.lam = mp.pi**2/12 - mp.log(2)**2 + sum(self.R)
        self.mu = mp.log(2) + sum(n*v for n, v in enumerate(self.R))
        self.p = -mp.expm1(-self.lam)
        self.uc = 1/self.p
        self.m = mp.exp(-self.lam)*self.mu/self.p
        self.kappa = 2*mp.exp(-self.lam)/(3*self.p)
        self.d = self.kappa/mp.gamma(-mp.mpf('1.5'))
        self.a2 = -mp.log(2)/2-mp.mpf(1)/4 + sum(n*(n-1)*v for n,v in enumerate(self.R))/2
        self.beta = mp.exp(-self.lam)/self.p*(self.a2-self.mu**2/2)
        self.kappa1 = mp.exp(-self.lam)/self.p*(mp.mpf(8)/15+2*self.mu/3)
        self.h2 = (self.m**2-self.m)/2-self.beta

    def tilt(self, t) -> dict:
        t = mp.mpf(t)
        if t == 0:
            return dict(t=t, r=mp.mpf(1), h=mp.mpf(0), mt=self.m, vt=mp.inf)
        if t < 0:
            raise ValueError('The numerical tilt is defined for t >= 0.')
        e = mp.exp(-t)
        s = mp.sqrt(-mp.expm1(-t))
        y = (1-s)/2
        A = mp.polylog(2, y)-mp.log(1-y)**2/2
        A += sum(v*e**n for n, v in enumerate(self.R))
        M = -mp.log((1+s)/2)+sum(n*v*e**n for n,v in enumerate(self.R))
        T = (1-s)/(2*s)+sum(n*n*v*e**n for n,v in enumerate(self.R))
        em1 = mp.expm1(A)
        r = self.p/(-mp.expm1(-A))
        mt = M/em1
        vt = T/em1-M*M*mp.exp(A)/em1**2
        assert mt > 0 and vt > 0
        return dict(t=t, r=r, h=mp.log(r), mt=mt, vt=vt)

    def kernels(self, a) -> tuple[mp.mpf, mp.mpf]:
        a = mp.mpf(a)
        def base(y):
            if y == 0:
                return mp.mpf(2) if a == 0 else mp.mpf(0)
            return 2*mp.exp(-y*y)*y**4/(a+y*y)**2
        def correction(y):
            x = y*y
            if x == 0:
                return mp.mpf(0)
            bracket = x*x/2-x-self.kappa1/self.kappa*x
            bracket -= 2*self.beta/self.m*x*x/(a+x)
            bracket -= self.kappa**2/self.m**2*x**3/(a+x)**2
            return base(y)*bracket
        return mp.quad(base, [0,1,3,mp.inf]), mp.quad(correction, [0,1,3,mp.inf])

    def float_q(self, N: int) -> np.ndarray:
        B, I = np.zeros(N+1), np.zeros(N+1)
        central = 1.0
        for n in range(1, N+1):
            central *= 1-1/(2*n)
            B[n] = central/(2*n)
            if n < len(self.R):
                B[n] += n*float(self.R[n])
            I[n] = (B[n]-np.dot(B[1:n], I[n-1:0:-1]))/n
        assert np.min(I) > -1e-15
        I[np.abs(I) < 1e-18] = 0
        return I/float(self.p)

    def constant_dict(self) -> dict:
        return {k: mp.nstr(getattr(self,k),45) for k in
                ['lam','mu','p','uc','m','kappa','d','a2','beta','kappa1','h2']}


def renewal(q: np.ndarray, mark: complex | float = 1.0,
            max_length: int | None = None) -> np.ndarray:
    N = len(q)-1
    dtype = complex if np.iscomplexobj(mark) else float
    U = np.zeros(N+1, dtype=dtype)
    U[0] = 1
    cutoff = N if max_length is None else max(0, min(max_length, N))
    for n in range(1, N+1):
        k = min(n, cutoff)
        U[n] = mark*np.dot(q[1:k+1], U[n-1:n-k-1:-1] if n > k else U[n-1::-1])
    return U


def moments(q: np.ndarray) -> tuple[float,float,float]:
    N = len(q)-1
    U, D, F = np.zeros(N+1), np.zeros(N+1), np.zeros(N+1)
    U[0] = 1
    for n in range(1,N+1):
        weights = q[1:n+1]
        U[n] = np.dot(weights,U[n-1::-1])
        D[n] = np.dot(weights,(U+D)[n-1::-1])
        F[n] = np.dot(weights,(2*D+F)[n-1::-1])
    mean = D[N]/U[N]
    var = (F[N]+D[N])/U[N]-mean*mean
    return float(U[N]),float(mean),float(var)


def write_csv(path: Path, rows: list[dict]):
    if not rows:
        return
    with path.open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=4096)
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if args.max_n < 256 or args.dps < 30:
        parser.error('--max-n must be >=256 and --dps >=30')
    args.output.mkdir(parents=True,exist_ok=True)
    start=time.time()
    arithmetic,S,I=arithmetic_counts(180)
    checks=exact_checks(arithmetic,S,I)
    model=Model(arithmetic,args.dps)
    for acheck in [mp.mpf('0.01'),mp.mpf(1),mp.mpf(10)]:
        integral,_=model.kernels(acheck)
        closed=mp.sqrt(mp.pi)*(1+acheck)-mp.pi*mp.sqrt(acheck)*(acheck+mp.mpf('1.5'))*mp.exp(acheck)*mp.erfc(mp.sqrt(acheck))
        assert abs(integral-closed) < mp.mpf(10)**(-args.dps+8)
    checks['kernel_integral_vs_erfc_closed_form']='PASS (high-precision, non-interval)'
    q=model.float_q(args.max_n)
    assert max(abs(q[n]*float(model.p)*4**n-I[n])/max(1,I[n]) for n in range(1,31)) < 3e-13
    checks['normalized_recurrence_vs_exact_through_30']='PASS'
    sizes=[n for n in [256,1024,4096] if n<=args.max_n]
    if args.max_n not in sizes:
        sizes.append(args.max_n)
    branch=[];chars=[];maxima=[];gaussian=[];inverses=[]
    for n in sizes:
        indices=np.arange(n+1)
        for nt in [0,1,4]:
            tilt=model.tilt(mp.mpf(nt)/n); r,mt=tilt['r'],tilt['mt']
            qt=q[:n+1]*float(r)*np.exp(-float(tilt['t'])*indices)
            un=float(renewal(qt)[-1])
            a=n*(1-1/r)/model.m
            K0,K1=model.kernels(a)
            pref=mp.exp(-nt)*model.kappa/(mp.pi*r*model.m**2)*n**(-mp.mpf('0.5'))
            pole=1/mt; k0=pole+pref*K0;k1=k0+pref*K1/n
            branch.append(dict(n=n,nt=nt,U=un,pole_error=float(pole-un),
                               K0_error=float(k0-un),K1_error=float(k1-un)))
        bn=(model.kappa*n/model.m)**(mp.mpf(2)/3)
        for sigma in [0,0.5,2]:
            tilt=model.tilt(mp.mpf(sigma)/bn)
            qt=q[:n+1]*float(tilt['r'])*np.exp(-float(tilt['t'])*indices)
            un=float(renewal(qt)[-1]); xi=1.0
            theta=xi*float(tilt['mt']/bn)
            cf=complex(np.exp(-1j*xi*n/float(bn))*renewal(qt,np.exp(1j*theta))[-1]/un)
            limiting=complex(mp.exp((sigma+1j*xi)**mp.mpf('1.5')-mp.mpf(sigma)**mp.mpf('1.5')
                                   -mp.mpf('1.5')*1j*xi*mp.sqrt(sigma)))
            chars.append(dict(n=n,sigma=sigma,cf_real=cf.real,cf_imag=cf.imag,
                              limit_real=limiting.real,limit_imag=limiting.imag,error=abs(cf-limiting)))
            for x in [1,2]:
                empirical=float(renewal(qt,max_length=math.floor(float(bn)*x))[-1]/un)
                tail=mp.quad(lambda y:mp.exp(-sigma*y)*y**(-mp.mpf('2.5')),[x,mp.inf])
                limiting_max=mp.exp(-tail/mp.gamma(-mp.mpf('1.5')))
                maxima.append(dict(n=n,sigma=sigma,x=x,cdf=empirical,
                                   limit=float(limiting_max),error=empirical-float(limiting_max)))
        t=mp.mpf(n)**(-mp.mpf(1)/4)
        tilt=model.tilt(t);qt=q[:n+1]*float(tilt['r'])*np.exp(-float(t)*indices)
        un,mean,var=moments(qt)
        cent=float(n/tilt['mt']);sd=float(mp.sqrt(n*tilt['vt']/tilt['mt']**3))
        cf=np.exp(-1j*cent/sd)*renewal(qt,np.exp(1j/sd))[-1]/un
        B=n*tilt['r']*model.d*t**mp.mpf('1.5')/tilt['mt']
        w=mp.mpf('2.5')*mp.lambertw(mp.mpf('0.4')*B**mp.mpf('0.4'))
        gumbel=float(renewal(qt,max_length=math.floor(float(w/t)))[-1]/un)
        refined_w=mp.findroot(lambda v:B*mp.gammainc(-mp.mpf('1.5'),v,mp.inf)-1,(w/2,w))
        refined_gumbel=float(renewal(qt,max_length=math.floor(float(refined_w/t)))[-1]/un)
        gaussian.append(dict(n=n,t=float(t),B=float(B),center=cent,mean=mean,
                             mean_shift_in_sd=(mean-cent)/sd,var_ratio=var/sd**2,
                             cf_error=abs(cf-math.exp(-.5)),gumbel_at_zero=gumbel,refined_gumbel_at_zero=refined_gumbel,
                             gumbel_limit=math.exp(-1)))
    for exponent in [2,3,4,5]:
        h=mp.mpf(10)**(-exponent);v=h/model.m
        t0=v;t1=v+model.kappa/model.m*v**mp.mpf('1.5')
        t2=t1+(mp.mpf('1.5')*model.kappa**2/model.m**2-model.h2/model.m)*v*v
        root=mp.findroot(lambda t:model.tilt(t)['h']-h,(t1*.9,t1*1.1))
        inverses.append(dict(h=float(h),t=float(root),order0_error=float(t0-root),
                             order1_error=float(t1-root),order2_error=float(t2-root)))
    for name,rows in [('branch_errors',branch),('tempered_characteristics',chars),
                      ('maximum_cdf',maxima),('gaussian_gumbel',gaussian),('inverse_errors',inverses)]:
        write_csv(args.output/(name+'.csv'),rows)
    summary={'status':'Finite exact checks and non-interval numerical diagnostics; no asymptotic proof by computation.',
             'python':sys.version,'numpy':np.__version__,'mpmath':mp.__version__,
             'platform':platform.platform(),'max_n':args.max_n,'dps':args.dps,
             'constants':model.constant_dict(),'checks':checks,'seconds':time.time()-start}
    (args.output/'verification.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
    (args.output/'oeis_exact_0_80.csv').write_text('n,S_n,I_n,N_n\n'+'\n'.join(
        f'{n},{S[n]},{I[n]},{arithmetic[n]}' for n in range(81))+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2))
    print('Branch diagnostics:',branch)
    print('Characteristic diagnostics:',chars)

if __name__=='__main__':
    main()
