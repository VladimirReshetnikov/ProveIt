#!/usr/bin/env python3
"""Reproducible finite verification; arbitrary precision, not interval certification.

Uses only the standard library, mpmath, and sympy. All checks raise exceptions,
so python -O does not disable any check. Sources are read only from local copies.
"""
from __future__ import annotations
import argparse, hashlib, json, math, platform, sys
from fractions import Fraction
from itertools import accumulate
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def close(a, b, digits, label):
    err = abs(a-b)/max(abs(a), abs(b), mp.mpf('1e-100000'))
    require(err < mp.power(10,-digits), f'{label}: relative error {mp.nstr(err,8)}')
    return err

def text(x, digits=65):
    return mp.nstr(x, digits)

def constants():
    h = 1/(1-mp.lambertw(mp.exp(-1)))
    k = (2*h-1)*(h-1)/2
    return h,k

def triangle(nmax):
    """P(n,p)=(n+1-p)P(n-1,p)+sum_{k<=n+1-p}P(n-1,k).
    Prefix sums cost O(nmax^2) integer operations and O(nmax) row storage.
    a[0]=None: the artificial b0=1/2 is not an OEIS count.
    """
    p = [0,1]
    a = [None,1]
    first_rows = [[1]]
    for n in range(2,nmax+1):
        s=[0]+list(accumulate(p[1:]))
        p=[0]+[(n+1-j)*(p[j] if j<n else 0)+s[min(n-1,n+1-j)] for j in range(1,n+1)]
        a.append(sum(p))
        if n<=10:
            first_rows.append(p[1:])
    return a,first_rows

def gf_coefficients(nmax):
    """Independent formal division N(z)/D(z) over fractions.Fraction.
    D=2-z+log(1-z), N=-(2-z)log(1-z)/(2z).
    D0=2, D1=-2, Di=-1/i for i>=2.
    """
    b=[Fraction(1,2)]
    for n in range(1,nmax+1):
        numerator=Fraction(1,n+1)-Fraction(1,2*n)
        b.append((numerator+2*b[n-1]+sum((b[n-j]/j for j in range(2,n+1)), Fraction(0)))/2)
    return b

def density(t):
    if t==0: return mp.mpf(1)
    if t==1: return mp.mpf(0)
    q=2*t-1
    return q*q/((q-t*(mp.log(t)-mp.log1p(-t)))**2+mp.pi**2*t*t)

def H(u):
    """w(exp(-u)), stable at tiny u using expm1; bounded at large u."""
    if u==0: return mp.mpf(0)
    if u < mp.mpf('0.5'):
        e=mp.expm1(u)
        q=-e+mp.log(e/u)
        return (1-e)**2/((mp.log(u)+1+q)**2+mp.pi**2)
    t=mp.exp(-u)
    ell=-u-mp.log(-mp.expm1(-u))
    q=2*t-1
    return q*q/((q-t*ell)**2+mp.pi**2*t*t)

def scaled_integral(N, r=0):
    """Integral exp(-v) v^r H(v/N) dv. No subtraction of dominant atom.
    Finite tail cutoff is pushed past working precision; this is NOT an
    interval quadrature or a certified tail bound. Precision-doubling checks
    are reported separately.
    """
    T=(mp.mp.dps+30)*mp.log(10)
    points=[mp.mpf(0),mp.mpf('.01'),mp.mpf('.1'),mp.mpf(1),mp.mpf(4),mp.mpf(16),mp.mpf(64),T]
    return mp.quad(lambda v: mp.exp(-v)*v**r*H(v/N), points)

def residual_integral(n):
    N=mp.mpf(n)+1
    return scaled_integral(N)/(2*N)

def residual_exact(n, an, digits=85):
    with mp.workdps(digits+math.ceil(float(n)*math.log10(1.386))+20):
        h,k=constants()
        r=mp.mpf(an)/mp.factorial(n+1)-k*h**n
        return +r

def symbolic_coefficients(J=2,K=6):
    u=sp.Symbol('u')
    A=sp.series((2-sp.exp(u))**2,u,0,J+1).removeO()
    q=sp.series(1-sp.exp(u)+sp.log((sp.exp(u)-1)/u),u,0,J+1).removeO()
    aa={(j,m):sp.expand(sp.series(A*q**m,u,0,J+1).removeO()).coeff(u,j) for j in range(J+1) for m in range(j+1)}
    C={}
    # Taylor coefficients of Gamma(j+1+alpha), using its log expansion.
    for j in range(J+1):
        g=[sp.factorial(j)]
        ell=[0,sp.harmonic(j)-sp.EulerGamma]+[(-1)**r*(sp.zeta(r)-sp.harmonic(j,r))/r for r in range(2,K+2)]
        for r in range(1,K+2):
            g.append(sp.expand(sum(s*ell[s]*g[r-s] for s in range(1,r+1))/r))
        moments=[sp.factorial(r)*g[r] for r in range(K+2)]
        for kk in range(K+1):
            expr=0
            for m in range(min(j,kk)+1):
                power=kk+1-m
                for r in range(power+1):
                    # Im (1+i*pi)^(power-r), avoiding symbolic assumptions.
                    d=power-r
                    imag=sum(sp.binomial(d,s)*(-1)**((s-1)//2)*sp.pi**s for s in range(1,d+1,2))
                    expr+=aa[j,m]*sp.binomial(kk+1,m)*sp.binomial(power,r)*moments[r]*imag/sp.pi
            C[j,kk]=sp.expand(expr)
    Aconst=1-sp.EulerGamma
    expected=[1,2*Aconst,3*Aconst**2-sp.pi**2/2,4*Aconst**3-2*sp.pi**2*Aconst-8*sp.zeta(3),5*Aconst**4-5*sp.pi**2*Aconst**2-40*Aconst*sp.zeta(3)+sp.pi**4/12]
    for kk, exp in enumerate(expected):
        require(sp.simplify(C[0,kk]-exp)==0,f'wrong supplied C0,{kk}')
    require(C[1,0]==-2,'C1,0')
    require(sp.simplify(C[1,1]-(-9+4*sp.EulerGamma))==0,'C1,1')
    return aa,C

def coef_num(e):
    return mp.mpf(str(sp.N(e,mp.mp.dps+8)))

def coefficient_function(j,L,aa):
    def f(v):
        if v==0: return mp.mpf(0)
        S=L-1-mp.log(v)-1j*mp.pi
        return mp.exp(-v)*v**j*mp.im(sum(coef_num(aa[j,m])/S**(m+1) for m in range(j+1)))/mp.pi
    T=(mp.mp.dps+30)*mp.log(10)
    return mp.quad(f,[0,.01,.1,1,4,16,64,T])

def envelope_log(x,h,k):
    return mp.log(k)+mp.loggamma(x+2)+x*mp.log(h)

def inverse_envelope_shift(n,an):
    # Extra precision resolves positive shift even at large n.
    with mp.workdps(90+math.ceil(n*math.log10(1.386))):
        h,k=constants()
        loga=mp.log(an)
        target=loga-envelope_log(n,h,k)
        def df(u):
            return mp.loggamma(n+u+2)-mp.loggamma(n+2)+u*mp.log(h)-target
        start=target/(mp.digamma(n+2)+mp.log(h))
        shift=mp.findroot(df,(start,start*mp.mpf('1.001')),solver='secant')
        return +shift

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-n',type=int,default=1000)
    parser.add_argument('--gf-n',type=int,default=250)
    parser.add_argument('--round-n',type=int,default=200)
    parser.add_argument('--output',type=Path,default=ROOT/'verification_results.json')
    parser.add_argument('--quick',action='store_true',help='skip continuous inverse/mixed-sector integrals')
    args=parser.parse_args()
    require(args.max_n>=max(args.gf_n,args.round_n,200),'max-n must cover all exact checks')
    mp.mp.dps=90
    h,k=constants()
    report={'notice':'Finite exact tests and arbitrary-precision numerical diagnostics, not a proof or interval certificate.',
        'software':{'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__},
        'parameters':{'max_n':args.max_n,'gf_n':args.gf_n,'round_n':args.round_n,'quick':args.quick},
        'constants':{'h':text(h,85),'k':text(k,85),'atom_weight_2k':text(2*k,85),'continuous_mass':text(1-2*k,85)}}
    a,rows=triangle(args.max_n)
    b=gf_coefficients(args.gf_n)
    for n in range(1,args.gf_n+1):
        require(b[n]*math.factorial(n+1)==a[n],f'GF/triangle mismatch at n={n}')
    oeis_path=ROOT/'oeis_b196275.txt'
    oeis=[]
    for line in oeis_path.read_text().splitlines():
        if line.strip() and not line.lstrip().startswith('#'):
            ns,ans=line.split(); n,an=int(ns),int(ans);oeis.append(n)
            require(a[n]==an,f'OEIS mismatch n={n}')
    require(oeis==list(range(1,201)),'unexpected OEIS b-file index range')
    report['exact_checks']={'triangle_vs_GF_indices':[1,args.gf_n],'triangle_vs_OEIS_indices':[1,200],
      'oeis_url':'https://oeis.org/A196275/b196275.txt','oeis_sha256':hashlib.sha256(oeis_path.read_bytes()).hexdigest(),
      'first_10_triangle_rows':rows,'first_12_b':[str(x) for x in b[:12]],
      'a_max_n_digit_count':len(str(a[-1]))}
    print('Exact GF/triangle/OEIS checks passed',flush=True)
    # All exact counts are local artifacts, not claimed as newly published data.
    exact_path=args.output.with_name(args.output.stem+'_exact_counts.json')
    exact_path.write_text(json.dumps({str(n):str(a[n]) for n in range(1,args.max_n+1)},indent=2)+'\n')
    report['exact_counts_file']=exact_path.name
    aa,C=symbolic_coefficients()
    report['symbolic_coefficients']={f'{j},{kk}':str(v) for (j,kk),v in C.items()}
    report['analytic_u_coefficients']={f'{j},{m}':str(v) for (j,m),v in aa.items()}
    print('Symbolic logarithmic coefficients passed',flush=True)
    moments=[]
    for n in [0,1,2,3,4,5,10,20,50,100,200,500,1000]:
        if n>args.max_n: continue
        r=residual_integral(n)
        rexact=mp.mpf('.5')-k if n==0 else residual_exact(n,a[n])
        err=close(r,rexact,65,f'spectral moment n={n}')
        moments.append({'n':n,'residual':text(r),'relative_difference_integral_vs_exact':text(err,8),
             'relative_spectral_correction':text(r/(k*h**n)),
             'working_dps_exact_subtraction':85+math.ceil(n*math.log10(1.386))+20})
    report['spectral_moments']=moments
    # Independently integrate in t at small indices, including atom mass.
    direct=[]
    for n in [0,1,2,4,10]:
        val=mp.quad(lambda t: t**n*density(t),[0,.1,.3,.5,.7,.9,.99,1])/2
        err=close(val,residual_integral(n),65,f'direct t integral n={n}')
        direct.append({'n':n,'residual_direct_t':text(val),'relative_difference_vs_scaled_v':text(err,8)})
    report['direct_t_moments']=direct
    print('Stable spectral moments passed',flush=True)
    # Bad fixed-precision subtraction is included as a cautionary diagnostic.
    cancel=[]
    for n in [100,200,500,1000]:
        if n>args.max_n:continue
        ref=residual_integral(n)
        with mp.workdps(50):
            hh,kk=constants();bad=mp.mpf(a[n])/mp.factorial(n+1)-kk*hh**n
        cancel.append({'n':n,'fixed_50_dps_residual':text(bad,18),'stable_residual':text(ref,18),'absolute_relative_error':text(abs(bad-ref)/ref,8)})
    report['cancellation_diagnostic']=cancel
    # Compare 65 and 90 digits for a sample of scaled integrals.
    stability=[]
    for n in [0,1000,10**24,10**96]:
        hi=residual_integral(n)
        with mp.workdps(65): lo=residual_integral(n)
        err=close(hi,lo,55,f'quadrature precision n={n}')
        stability.append({'n':str(n),'relative_65_vs_90_dps':text(err,8)})
    report['quadrature_precision_stability']=stability
    asym=[]
    for n in [100,1000,10**6,10**12,10**24,10**48,10**96]:
        N=mp.mpf(n)+1;L=mp.log(N);r=residual_integral(n)
        norm=2*N*L*L*r
        vals=[];part=mp.mpf(0)
        for kk in range(7):
            part+=coef_num(C[0,kk])/L**kk
            vals.append({'last_k':kk,'approx_normalized':text(part,35),'relative_error':text((part-norm)/norm,15)})
        asym.append({'n':str(n),'residual':text(r,40),'normalized_2Nlog2N_residual':text(norm,40),'truncations':vals})
    report['inverse_log_expansion']=asym
    print('Inverse-log numerical table complete',flush=True)
    rounding=[]
    # This checks every integer in a finite range, independent of the all-n proof.
    maxshift=(-1,mp.mpf(0));first_forward_fail=None
    for n in range(1,args.round_n+1):
        shift=inverse_envelope_shift(n,a[n])
        require(0<shift<mp.mpf('.5'),f'inverse rounding failed n={n}')
        if shift>maxshift[1]:maxshift=(n,shift)
        with mp.workdps(90+math.ceil(n*math.log10(1.386))):
            hh,kk=constants();r=residual_exact(n,a[n]);err=mp.factorial(n+1)*r
            if first_forward_fail is None and err>=mp.mpf('.5'): first_forward_fail=n
        if n in [1,2,3,4,5,10,20,50,100,200,args.round_n]:
            rounding.append({'n':n,'envelope_inverse_minus_n':text(shift),'a_n_minus_envelope':text(err,30)})
    report['rounding']={'checked_all_indices':[1,args.round_n],
       'max_inverse_shift_index':maxshift[0],'max_inverse_shift':text(maxshift[1]),
       'first_failure_round_envelope_to_count':first_forward_fail,'selected_rows':rounding}
    if not args.quick:
        mixed=[]
        for n in [100,1000,10000,1000000]:
            N=mp.mpf(n)+1;L=mp.log(N);r=residual_integral(n);s=mp.mpf(0);terms=[]
            for j in range(3):
                Fj=coefficient_function(j,L,aa);s+=Fj/(2*N**(j+1))
                terms.append({'J':j,'F_J':text(Fj,40),'relative_error':text((s-r)/r,20),
                    'remainder_times_N_Jplus2_log2N':text((r-s)*N**(j+2)*L**2,30)})
            mixed.append({'n':n,'truncations':terms})
        report['mixed_power_log_sectors']=mixed
        print('Mixed-sector numerical table complete',flush=True)
        inv=[]
        for Xint in [5,10,25,50,100]:
            dps=95+math.ceil(3*Xint*math.log10(1.386))
            with mp.workdps(dps):
                X=mp.mpf(Xint);hh,kk=constants();lh=mp.log(hh)
                I=scaled_integral(X)/X
                Ip=-scaled_integral(X,1)/X**2
                S=hh/(2*kk)*hh**(-X)*I
                Sp=hh/(2*kk)*hh**(-X)*(Ip-lh*I)
                p=mp.digamma(X+1)+lh;q=mp.polygamma(1,X+1)
                u1=-S/p;u2=S*Sp/p**2+S*S/(2*p)-q*S*S/(2*p**3)
                def residual_u(u):
                    SI=hh/(2*kk)*hh**(-(X+u))*scaled_integral(X+u)/(X+u)
                    return mp.loggamma(X+u+1)-mp.loggamma(X+1)+u*lh+mp.log1p(SI)
                full=mp.findroot(residual_u,(u1,u1+u2),solver='secant',tol=mp.power(10,-dps+15))
                require(full<0,f'continuous inverse shift wrong sign at X={Xint}')
                require(abs(full-u1-u2)<abs(full-u1),f'second inverse sector fails improvement X={Xint}')
                inv.append({'X_star':Xint,'dps':dps,'S':text(S,45),'full_inverse_shift':text(full,55),
                    'first_sector':text(u1,55),'second_sector':text(u2,55),
                    'error_after_first_over_S2_div_p':text((full-u1)*p/S**2,25),
                    'error_after_second_over_S3_div_p':text((full-u1-u2)*p/S**3,25),
                    'relative_error_after_first':text((u1-full)/full,25),
                    'relative_error_after_second':text((u1+u2-full)/full,25)})
            print(f'Continuous inverse checked X*={Xint}',flush=True)
        report['continuous_inverse_exponential_corrections']=inv
    report['status']='all explicit exception-based checks passed'
    args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'Wrote {args.output}',flush=True)

if __name__=='__main__':
    main()
