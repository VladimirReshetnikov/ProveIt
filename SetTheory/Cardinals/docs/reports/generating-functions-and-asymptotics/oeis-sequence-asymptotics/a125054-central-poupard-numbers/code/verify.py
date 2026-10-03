#!/usr/bin/env python3
"""Reproduce exact checks and non-interval numerical diagnostics for the article.

Run from any directory.  The output directory defaults to this package's data/.
Requires Python >= 3.10, mpmath and sympy; no network access or external data.
Floating-point diagnostics are not proof certificates.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
from typing import Callable
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def tangent_numbers(nmax: int) -> list[int]:
    t = [1]
    for n in range(1, nmax + 1):
        t.append(sum(math.comb(2*n, 2*j+1) * t[j] * t[n-1-j]
                     for j in range(n)))
    return t

def transform(t: list[int], n: int, c: int = 1) -> int:
    return sum(math.comb(n,k)*c**(n-k)*t[k] for k in range(n+1))

def s_fraction(weights: Callable[[int], int], degree: int) -> list[int]:
    """Truncated S-fraction via exact formal reciprocals, enough levels for degree."""
    tail = [1] + [0]*degree
    for level in range(degree, 0, -1):
        w = weights(level)
        out = [1] + [0]*degree
        for r in range(1, degree+1):
            out[r] = w*sum(tail[j]*out[r-1-j] for j in range(r))
        tail = out
    return tail

def correction_polynomials(order: int):
    z = sp.Symbol('z')
    C = [sp.Integer(0)]*(order+1)
    for j in range(order+1):
        inv = [sp.Integer(1)] + [sp.Integer(0)]*(order-j)
        for ell in range(j):
            q = sp.Rational(1,2)-ell
            inv = [sp.expand(sum(inv[k]*(-q)**(r-k) for k in range(r+1)))
                   for r in range(order-j+1)]
        for r in range(j, order+1):
            C[r] += (z/4)**j/sp.factorial(j)*inv[r-j]
    C = [sp.expand(v) for v in C]
    ell = [sp.Integer(0)]
    for r in range(1,order+1):
        ell.append(sp.expand(C[r] - sum(k*ell[k]*C[r-k] for k in range(1,r))/r))
    h = [sp.Integer(0)]
    for r in range(1,order+1):
        stir = sp.Rational((-1)**(r+1),r*2**r)
        if r % 2:
            k=(r+1)//2
            stir += sp.bernoulli(2*k)/(2*k*(2*k-1)*2**(2*k-1))
        h.append(sp.expand(ell[r]+stir))
    return z,C,ell,h

def H(n: int, z: mp.mpf) -> mp.mpf:
    term = mp.mpf(1)
    out = term
    for j in range(1,n+1):
        term *= z/(4*j*(mp.mpf(n)+mp.mpf('1.5')-j))
        out += term
    return out

def sci(v: mp.mpf, digits: int = 4) -> str:
    return mp.nstr(v, digits, min_fixed=-2, max_fixed=4)

def texnum(v: mp.mpf, digits: int = 4) -> str:
    st=sci(v,digits)
    if 'e' in st:
        m,e=st.split('e')
        return m + r'\times 10^{' + str(int(e)) + '}'
    return st

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=ROOT/'data')
    parser.add_argument('--max-n',type=int,default=4096)
    parser.add_argument('--dps',type=int,default=90)
    args=parser.parse_args()
    if args.max_n<256 or args.dps<80:
        parser.error('--max-n must be >=256 and --dps >=80')
    out=args.output_dir
    out.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=args.dps
    alpha=mp.pi/2
    t=tangent_numbers(256)
    an=[transform(t,n) for n in range(len(t))]
    reference=[1,3,21,327,9129,396363,24615741,2068052367,225742096209,
               31048132997523,5252064083753061,1071525520294178007,
               259439870666594250489,73542221109962636293083,
               24125551094579137082039181,9068240688454120376775401247,
               3871645204706420218816959159969]
    check(an[:len(reference)]==reference,'OEIS initial values')
    N=48
    check(s_fraction(lambda j:j*(j+1),N)==t[:N+1],'tangent S-fraction')
    beta=lambda j: (j+2)**2 if j%2 else j*(j+2)
    B=s_fraction(beta,N)
    conjectured=[1]+[1+2*sum(B[:n]) for n in range(1,N+1)]
    check(conjectured==an[:N+1],'Bala conjecture coefficients')
    check(all(v%9==3 for v in an[1:]),'modulo 9 congruence')
    # Independent Poupard row recurrence from its two initial entries.
    row=[1]
    for n in range(1,25):
        r=[sum(row),3*sum(row)]
        for k in range(2,2*n+1):
            r.append(2*r[-1]-r[-2]-4*row[k-2])
        check(r==r[::-1] and r[n]==an[n],f'Poupard row {n}')
        row=r
    # All-index polynomial identities behind the contractions.
    k=sp.Symbol('k',integer=True,positive=True)
    check(sp.expand(4*k*(k+1)+(2*k+3)**2-(8*(k+1)**2+1))==0,
          'contracted diagonal')
    check(sp.expand((2*k+1)**2*4*k*(k+1)-4*k*(k+1)*(2*k+1)**2)==0,
          'contracted off-diagonal')
    det_values=[]
    for c in (0,1,3):
        v=[transform(t,n,c) for n in range(12)]
        b=[sum(math.comb(n,j)*c**(n-j)*t[j+1]//2 for j in range(n+1))
           for n in range(12)]
        for n in range(1,7):
            D=sp.det(sp.Matrix(n,n,lambda i,j:v[i+j]))
            E=sp.prod((4*j*j*(4*j*j-1))**(n-j) for j in range(1,n))
            check(D==E,f'Hankel A c={c}, N={n}')
            DB=sp.det(sp.Matrix(n,n,lambda i,j:b[i+j]))
            EB=sp.prod((4*j*(j+1)*(2*j+1)**2)**(n-j) for j in range(1,n))
            check(DB==EB,f'Hankel B c={c}, N={n}')
            if c==1:det_values.append(str(D))
    z,C,ell,h=correction_polynomials(8)
    check(C[1]==z/4 and sp.expand(C[3]-z/16-z**3/384)==0,'explicit C')
    check(h[1]==sp.Rational(13,24)+z/4,'h1')
    check(h[2]==-sp.Rational(1,8)-z/8,'h2')
    check(h[3]==sp.Rational(119,2880)+z/16+z*z/32,'h3')
    # Derive L_1 independently from derivatives of the saddle phase.
    u,tau,a,s=sp.symbols('u tau a s',positive=True)
    phase=sp.log(tau+u*u)-a*u
    subst={u:s/a,tau:s*(2-s)/a**2}
    kap=a*a*(s-1)/s
    p3=sp.factor(sp.diff(phase,u,3).subs(subst))
    p4=sp.factor(sp.diff(phase,u,4).subs(subst))
    L1=sp.factor(p3/(2*(s/a)*kap**2)+p4/(8*kap**2)+5*p3*p3/(24*kap**3))
    L1_expected=(2*s**3+18*s**2-60*s+45)/(24*(s-1)**3)
    check(sp.simplify(L1-L1_expected)==0,'L1 from Gaussian expansion')
    # Independent moment integration, not a test of a large-n approximation.
    quadrature=[]
    for n in (0,1,3,6):
        c=mp.mpf('1.25')
        exact=sum(mp.mpf(math.comb(n,j))*c**(n-j)*t[j] for j in range(n+1))
        integ=mp.quad(lambda y:(c+y*y)**n*y/mp.sinh(alpha*y) if y else c**n/alpha,
                      [0,1,4,16,mp.inf])
        err=abs(integ/exact-1)
        check(err<mp.mpf('1e-65'),'moment integral check')
        quadrature.append({'n':n,'relative_error':str(err)})
    # Fixed-c asymptotics: exact integers versus logarithmic truncations.
    hfun=[None]+[sp.lambdify(z,v,'mpmath') for v in h[1:]]
    fixed=[]
    fixed_tex=[]
    for n in (10,25,50,100,200):
        log_exact=mp.log(an[n])
        base=2*n*mp.log(2*n/(alpha*mp.e))+mp.mpf('1.5')*mp.log(n)+mp.log(8*mp.sqrt(mp.pi)/alpha**2)
        errs=[]
        for order in (0,1,3,6):
            la=base+sum(hfun[r](alpha**2)/mp.mpf(n)**r for r in range(1,order+1))
            errs.append(abs(mp.expm1(la-log_exact)))
        fixed.append({'n':n,'relative_errors':{str(o):str(e) for o,e in zip((0,1,3,6),errs)}})
        fixed_tex.append(str(n)+' & '+' & '.join('$'+texnum(e)+'$' for e in errs)+r' \\')
    (out/'fixed_table.tex').write_text('\n'.join(fixed_tex)+'\n',encoding='utf-8')
    # Exact-sector identity and its positive remainder bound, with full integer A.
    sectors=[]
    for n in (8,16,32):
        F=2*mp.gamma(2*n+2)/alpha**(2*n+2)
        total=mp.mpf(an[n])/F
        h1=H(n,alpha**2)
        h3=mp.power(3,-2*n-2)*H(n,9*alpha**2)
        rem=total-h1-h3
        bound=(1+mp.mpf(5)/2)*mp.power(5,-2*n-2)*H(n,25*alpha**2)
        check(rem>0 and rem<=bound,'positive q>=5 remainder')
        sectors.append({'n':n,'normalized_total':str(total),'q1':str(h1),
                        'tail_after_q1':str(total-h1),
                        'q3':str(h3),'q5_remainder':str(rem),'q5_bound':str(bound)})
    # Accurate log moments; all summands in the transition diagnostic are positive.
    lt=[mp.log(v) for v in t]
    for j in range(len(lt),args.max_n+1):
        r=2*j+2
        lt.append(mp.log(2)+mp.loggamma(r)-r*mp.log(alpha)+
                  mp.log((1-mp.power(2,-r))*mp.zeta(r)))
    star=mp.findroot(lambda v:2-v-2*mp.exp(-v),(mp.mpf('1.5'),mp.mpf('1.7')))
    ts=star*(2-star)/alpha**2
    ds=alpha**2/(2*(2-star))
    K=lambda v:2*mp.sqrt(2*mp.pi)*v**mp.mpf('1.5')/(alpha**2*mp.sqrt(v-1))
    Ks=K(star)
    def norm_sum(n:int, tau:mp.mpf):
        c=tau*n*n
        logs=[]
        lc=mp.log(c)
        logbin=mp.mpf(0)
        for j in range(n+1):
            if j:logbin += mp.log(n-j+1)-mp.log(j)
            logs.append(logbin+lt[j]-j*lc)
        top=max(logs)
        weights=[mp.exp(v-top) for v in logs]
        den=mp.fsum(weights)
        R=mp.exp(top)*den
        return R, 1/R, mp.fsum(j*weights[j] for j in range(n+1))/(n*den)
    critical=[]
    crittex=[]
    ns=sorted(set([128,512,2048,args.max_n]))
    ns=[n for n in ns if n<=args.max_n]
    for n in ns:
        for w in (-2,0,2):
            tauv=ts+(mp.mpf('1.5')*mp.log(n)+mp.log(Ks)+w)/(ds*n)
            R,p0,mean=norm_sum(n,tauv)
            sv=1+mp.sqrt(1-alpha**2*tauv)
            delta=mp.log(2/(2-sv))-sv
            lv=(2*sv**3+18*sv**2-60*sv+45)/(24*(sv-1)**3)
            approx=1+2/(tauv*n)+K(sv)*n**mp.mpf('1.5')*mp.exp(n*delta)*(1+lv/n)
            limit=1+mp.exp(-w)
            err=abs(approx/R-1)
            critical.append({'n':n,'w':w,'tau':str(tauv),'normalized_moment':str(R),
                             'limit':str(limit),'two_contribution_relative_error':str(err),
                             'probability_k0':str(p0),'mean_k_over_n':str(mean)})
            crittex.append(f'{n} & {w} & {mp.nstr(R,10)} & {mp.nstr(limit,10)} & $'+texnum(err)+r'$ \\')
    (out/'critical_table.tex').write_text('\n'.join(crittex)+'\n',encoding='utf-8')
    inverse=[]
    invtex=[]
    for n in (10,25,50,100,200):
        L=mp.log(an[n]); W=mp.lambertw(L/(alpha*mp.e)); x0=L/(2*W)
        D0=-(mp.mpf('1.5')*mp.log(x0)+mp.log(8*mp.sqrt(mp.pi)/alpha**2))/(2*(W+1))
        D1=-(D0*D0+mp.mpf('1.5')*D0+mp.mpf(13)/24+alpha**2/4)/(2*x0*(W+1))
        errors=[abs(x0-n),abs(x0+D0-n),abs(x0+D0+D1-n)]
        inverse.append({'n':n,'absolute_errors':[str(e) for e in errors]})
        invtex.append(str(n)+' & '+' & '.join('$'+texnum(e)+'$' for e in errors)+r' \\')
    (out/'inverse_table.tex').write_text('\n'.join(invtex)+'\n',encoding='utf-8')
    # Complex roots: exact integer coefficients, normalized reverse Horner.
    # Residuals are numerical diagnostics, not certified root enclosures.
    roots=[]
    roottex=[]
    for n in (32,64,128,256):
        coefficients=[mp.mpf(math.comb(n,k))*t[k] for k in range(n+1)]
        def root_function(w):
            tauv=ts+(mp.mpf('1.5')*mp.log(n)+mp.log(Ks)+w)/(ds*n)
            inv=1/(tauv*n*n)
            val=mp.mpc(0)
            for v in reversed(coefficients):
                val=val*inv+v
            return val
        wr=mp.findroot(root_function,(mp.pi*1j,mp.pi*1j+mp.mpf('.5')),
                       tol=mp.mpf('1e-60'))
        residual=abs(root_function(wr))
        check(residual<mp.mpf('1e-55'),'complex-root numerical residual')
        roots.append({'n':n,'real_w':str(mp.re(wr)),'imag_w':str(mp.im(wr)),
                      'normalized_residual':str(residual)})
        roottex.append(str(n)+' & '+mp.nstr(mp.re(wr),10)+' & '+
                       mp.nstr(mp.im(wr),10)+r' \\')
    (out/'zeros_table.tex').write_text('\n'.join(roottex)+'\n',encoding='utf-8')
    # Universality diagnostics on explicit gamma moments, alpha=1.
    general=[]
    for power,shape in ((mp.mpf('1.5'),mp.mpf('.25')),
                        (mp.mpf(2),mp.mpf(1)),(mp.mpf(3),mp.mpf(2))):
        sg=mp.findroot(lambda v:power-v-power*mp.exp(-v),
                       (power-mp.mpf('.4'),power-mp.mpf('.1')))
        check(power-1<sg<power,'nonzero critical root in universal model')
        tg=sg**(power-1)*(power-sg)
        dg=1/(power*sg**(power-2)*(power-sg))
        kg=sg**(shape-1)/mp.gamma(shape)*mp.sqrt(2*mp.pi*sg/(sg-power+1))
        for n in sorted({256, min(1024,args.max_n),args.max_n}):
            tauv=tg+((shape-mp.mpf('.5'))*mp.log(n)+mp.log(kg))/(dg*n)
            logc=mp.log(tauv*n**power)
            lbin=mp.mpf(0)
            vals=[]
            for k in range(n+1):
                if k:lbin+=mp.log(n-k+1)-mp.log(k)
                vals.append(lbin+mp.loggamma(power*k+shape)-mp.loggamma(shape)-k*logc)
            top=max(vals)
            ws=[mp.exp(v-top) for v in vals]
            den=mp.fsum(ws)
            R=mp.exp(top)*den
            general.append({'p':str(power),'gamma_shape':str(shape),'n':n,
                's_star':str(sg),'normalized_moment_at_w0':str(R),
                'target_limit':'2','absolute_error':str(abs(R-2))})
    pp,ss=sp.symbols('p s')
    vv=(ss/pp)*(1-ss/pp)+(pp-ss)**2/pp**2*ss/(ss-pp+1)
    check(sp.factor(vv-ss*(pp-ss)/(pp**2*(ss-pp+1)))==0,
          'general Gaussian variance identity')
    result={
        'status':'all exact checks passed; floating-point outputs are diagnostics, not interval certificates',
        'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,
        'dps':args.dps,'max_n':args.max_n,
        'exact_checks':{'oeis_initial_terms':len(reference),'tangent_cf_degree':N,
            'conjectured_cf_degree':N,'congruence_through_n':256,'poupard_rows':24,
            'hankel_orders':list(range(1,7)),'hankel_shifts':[0,1,3],
            'symbolic_expansion_order':8,'symbolic_L1':'passed'},
        'constants':{'alpha':str(alpha),'s_star':str(star),'tau_star':str(ts),
            'd_star':str(ds),'K_star':str(Ks),'bulk_fraction_star':str(star/2),
            'bulk_variance_star':str(star*(2-star)/(4*(star-1)))},
        'polynomials':{'C':[str(v) for v in C],'logH':[str(v) for v in ell],
                       'h':[str(v) for v in h],'L1':str(L1)},
        'hankel_determinants_A_c1':det_values,
        'quadrature':quadrature,'fixed_asymptotics':fixed,'sectors':sectors,
        'critical_window':critical,'inverse':inverse,
        'complex_roots':roots,'universal_gamma_diagnostics':general,
    }
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    coefftex=[]
    for r in range(1,7):
        coefftex.append(r'\ell_{'+str(r)+r'}(z)&='+sp.latex(ell[r])+r'\\')
    (out/'log_coefficients.tex').write_text('\n'.join(coefftex)+'\n',encoding='utf-8')
    print('PASS: exact continued fractions, Poupard rows, congruence and Hankel determinants.')
    print('PASS: symbolic coefficients through order 8 and independent saddle L1 identity.')
    print('PASS: high-precision moment integrals and positive sector-tail diagnostics.')
    print(f'Wrote diagnostic tables and verification.json to {out}')
    print('s_* =',mp.nstr(star,35),' tau_* =',mp.nstr(ts,35))
    print('PASS: complex-root residual diagnostics and general variance identity.')
    print('No Lean formalization or interval floating-point certification is claimed.')

if __name__=='__main__':
    main()
