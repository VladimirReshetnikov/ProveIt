#!/usr/bin/env python3
"""Finite exact regressions and non-interval numerical diagnostics.
Outputs must go to a new/empty directory. Universal claims are proved in article.tex.
"""
from __future__ import annotations
import argparse, csv, json, math, platform, sys
from fractions import Fraction as F
from pathlib import Path
from typing import Sequence
import mpmath as mp
import numpy as np
import sympy as sp


def conv(a: Sequence[F], b: Sequence[F], n: int) -> list[F]:
    return [sum((a[j]*b[k-j] for j in range(k+1)), F(0)) for k in range(n+1)]


def exp_series(a: Sequence[F], n: int) -> list[F]:
    assert a[0] == 0
    b=[F(1)]+[F(0)]*n
    for k in range(1,n+1):
        b[k]=sum((j*a[j]*b[k-j] for j in range(1,k+1)),F(0))/k
    return b


def fixed_point(s: int, u: int, n: int) -> list[F]:
    v=[F(0)]*(n+1)
    for _ in range(n):
        w=[x/(2*u) for x in conv(v,v,n)]
        for j in range(1,n+1):
            ev=exp_series([j*x for x in v],n-j)
            for k in range(n-j+1): w[j+k]+=ev[k]/(u*j**s)
        v=w
    return v


def exact_lift(s: int, u: int, n: int) -> list[F]:
    h=[F(0)]*(n+1)
    for k in range(1,n+1):
        h[k]=(F(1,k**s)+sum((h[j]*h[k-j] for j in range(1,k)),F(0))/2)/u
    return h


def finite_formula(s: int, u: int, n: int) -> F:
    base=[F(0)]+[F(1,j**s) for j in range(1,n+1)]
    powers=[F(1)]+[F(0)]*n; total=F(0)
    for k in range(1,n+1):
        powers=conv(powers,base,n)
        inner=sum((F(math.comb(k+j-1,j)*n**(k-1-j),
            math.factorial(k-1-j)*2**j*u**(k+j)) for j in range(k)),F(0))
        total+=powers[n]*inner/k
    return total


def write_csv(path: Path, rows: list[dict]) -> None:
    if rows:
        with path.open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)


def exact_checks(out: Path) -> dict:
    assertions=0; rows=[]
    for s in (2,3,4):
        for u in (1,2,3):
            h=exact_lift(s,u,10);v=fixed_point(s,u,10)
            for n in range(1,11):
                a=exp_series([n*x for x in h],n)[n]/n
                assert a==v[n];assertions+=1
                assert a==finite_formula(s,u,n);assertions+=1
                assert a>0;assertions+=1
                rows.append({'s':s,'u':u,'n':n,'a_n':str(a)})
    z,A,H=sp.symbols('z A H');Q=[sp.Integer(1)]
    for k in range(1,5):
        Q.append(sp.expand(-sp.Rational(1,2*k)*sp.series(
          (1+z)**(-sp.Rational(3,2))*(A+sp.log(1+z))**k,z,0,k).removeO().coeff(z,k-1)))
    U=sp.Integer(1)
    for _ in range(5): U=sp.series(1+H*(A+sp.log(U)),H,0,5).removeO().expand()
    root=sp.series(U**(-sp.Rational(1,2)),H,0,5).removeO().expand()
    for k in range(5):
        assert sp.expand(root.coeff(H,k)-Q[k])==0;assertions+=1
    g=[sp.Integer(1),*sp.symbols('g1:5')];P=[]
    for m in range(5):
        total=0
        for j in range(m+1):
            poly=Q[m-j]
            for ell in range(j):poly=sp.diff(poly,A)-(m-j+ell+sp.Rational(1,2))*poly
            total+=(-1)**j*g[j]*poly/sp.factorial(j)
        P.append(sp.expand(total))
    # Independent substitution L -> L-y, followed by Hankel moments y^j -> g_j.
    y=sp.symbols('y');shifted=0
    for k in range(5):
        shifted+=H**k*sp.series((1-y*H)**(-k-sp.Rational(1,2))*
          Q[k].subs(A,A+sp.log(1-y*H)),H,0,5-k).removeO()
    shifted=sp.expand(shifted)
    for m in range(5):
        raw=sp.Poly(shifted.coeff(H,m),y)
        poly=sum(co*g[j] for (j,),co in raw.terms())
        assert sp.expand(poly-P[m])==0;assertions+=1
    D,p,t1=sp.symbols('D p t1')
    assert sp.expand(P[1].subs({A:D+p,g[1]:p})+D/2)==0;assertions+=1
    assert sp.expand(P[2].subs({A:D+p,g[1]:p,g[2]:p*p-t1})-
      (3*D**2/sp.Integer(8)-D/2-3*t1/sp.Integer(8)))==0;assertions+=1
    c,B=sp.symbols('c B',nonzero=True);a=-2*c/3;b=7*c*c/9+2/(3*B)
    U=1+a*z+b*z*z
    res=sp.series(U**sp.Rational(3,2)+c*z*U**2-z*z*U/B-1,z,0,3).removeO().expand()
    for k in (0,1,2):
        assert sp.simplify(res.coeff(z,k))==0;assertions+=1
    assert sp.simplify(sp.gamma(-sp.Rational(3,2))-4*sp.sqrt(sp.pi)/3)==0;assertions+=1
    # Use the exact trigamma recurrence, not special-function simplification heuristics.
    trigamma_minus_half=sp.pi**2/2+1/(-sp.Rational(1,2))**2
    assert sp.expand(trigamma_minus_half-(4+sp.pi**2/2))==0;assertions+=1
    for k in range(5):
        assert sp.Poly(P[k],A).coeff_monomial(A**k)==sp.binomial(-sp.Rational(1,2),k);assertions+=1
    # Critical s=4 logarithmic correction: exact balance of X^(3/2) log X.
    C=sp.symbols('C', positive=True);Bpos=sp.symbols('Bpos', positive=True)
    bcurv=C/(2*Bpos);aa=sp.sqrt(2*Bpos/C);dd=-Bpos/(6*C*C)
    assert sp.simplify(2*bcurv*aa*dd+aa**3/(12*Bpos))==0;assertions+=1
    write_csv(out/'exact_coefficients.csv',rows)
    (out/'marginal_polynomials.txt').write_text('\n'.join(
      [f'Q_{k}(A) = {Q[k]}' for k in range(5)]+[f'P_{k}(A) = {P[k]}' for k in range(5)])+'\n')
    return {'assertions_passed':assertions,'scope':
      'Rational comparisons through n=10; Lambert/Hankel polynomials through degree 4; stated finite local identities.'}


def model(s: str, critical: bool=True, kappa: str='1', prefix: str='0') -> dict:
    ss,kk,pp=map(mp.mpf,(s,kappa,prefix));aa=kk*mp.zeta(ss)+pp;bb=kk*mp.zeta(ss-1)+pp
    w=bb if critical else 2*bb;uu=mp.sqrt(2*aa+w*w)
    return {'s':ss,'kappa':kk,'prefix':pp,'A':aa,'B':bb,'w':w,'u':uu,
      'vb':uu-w,'R':mp.exp(w-uu),'critical':critical}


def numerical_lift(m: dict, n: int) -> np.ndarray:
    ld=np.longdouble;s=ld(str(m['s']));kap=ld(str(m['kappa']));pre=ld(str(m['prefix']));u=ld(str(m['u']))
    h=np.zeros(n+1,dtype=ld)
    for k in range(1,n+1):
        fk=kap/ld(k)**s+(pre if k==1 else ld(0))
        h[k]=(fk+np.dot(h[1:k],h[k-1:0:-1])/2)/u
    return h


def probability_ld(h: np.ndarray, vb: mp.mpf, n: int) -> np.longdouble:
    ld=np.longdouble;exponent=-ld(n)*ld(str(vb))
    if exponent<np.log(np.finfo(ld).tiny)+20:raise FloatingPointError('insufficient exponent range')
    p=np.zeros(n+1,dtype=ld);p[0]=np.exp(exponent);jh=np.arange(n+1,dtype=ld)*h[:n+1]
    for k in range(1,n+1):p[k]=ld(n)/k*np.dot(jh[1:k+1],p[k-1::-1])
    if not np.isfinite(p[n]) or p[n]<=0:raise FloatingPointError('invalid computed probability')
    return p[n]/n


def probability_mp(m: dict, n: int) -> mp.mpf:
    h=[mp.mpf(0)]*(n+1)
    for k in range(1,n+1):
        fk=m['kappa']/mp.mpf(k)**m['s']+(m['prefix'] if k==1 else 0)
        h[k]=(fk+mp.fsum(h[j]*h[k-j] for j in range(1,k))/2)/m['u']
    p=[mp.exp(-n*m['vb'])]+[mp.mpf(0)]*n
    for k in range(1,n+1):p[k]=mp.mpf(n)/k*mp.fsum(j*h[j]*p[k-j] for j in range(1,k+1))
    return p[n]/n


def asymptotics(m: dict, n: int) -> tuple[mp.mpf,mp.mpf,mp.mpf]:
    s=m['s'];B=m['B'];kap=m['kappa'];w=m['w'];N=mp.mpf(n)
    if not m['critical']:
        lead=kap/(w*(1-B/w)**s)*N**(-s);return lead,lead,lead
    if s<3:
        alpha=s-1;d=(B/(kap*mp.gamma(-alpha)))**(1/alpha)
        lead=-d/mp.gamma(-1/alpha)*N**(-1-1/alpha);corr=lead
        if s==mp.mpf('2.5') and kap==1 and m['prefix']==0:
            G=mp.gamma(-alpha);c=(1+mp.zeta(s-2))/(2*G);K=7*c*c/9+2/(3*B)
            corr=lead-K*d*d/mp.gamma(-mp.mpf(4)/3)*N**(-mp.mpf(7)/3)
        return lead,corr,corr
    if s>3:
        C2=kap*mp.zeta(s-2)+m['prefix'];lead=mp.sqrt(B/(2*mp.pi*(1+C2)))*N**(-mp.mpf('1.5'))
        corr=lead
        if s==4:
            corr+=kap*B/(6*(1+C2)**2)*N**(-2)
        return lead,corr,corr
    K=B/kap;b0=mp.mpf('1.5')+(1+m['prefix'])/kap;L=mp.log(N)
    D=mp.log(L)+2*b0-2+mp.euler-mp.log(K)
    lead=mp.sqrt(K/mp.pi)*N**(-mp.mpf('1.5'))/mp.sqrt(L)
    first=lead*(1-D/(2*L))
    second=lead*(1-D/(2*L)+(3*D*D/8-D/2-3*(4+mp.pi**2/2)/8)/L**2)
    return lead,first,second


def local_checks(out: Path) -> dict:
    rows=[];identities=[]
    def f(m,t):return m['kappa']*mp.polylog(m['s'],t)+m['prefix']*t
    for ss,crit,kap,pre in [('2.5',True,'1','0'),('3',True,'1','0'),('4',True,'1','0'),
                           ('3',False,'1','0'),('3',True,'2','0.5')]:
        m=model(ss,crit,kap,pre)
        for tau in (mp.mpf('1e-4'),mp.mpf('1e-8'),mp.mpf('1e-12')):
            X=tau-(mp.sqrt(m['u']**2-2*f(m,mp.exp(-tau)))-m['w'])
            v=m['vb']+X-tau;r=m['R']*mp.exp(-X)
            resid=m['u']*v-v*v/2-f(m,r*mp.exp(v));assert abs(resid)<mp.mpf('1e-70')
            if not crit:approx=(1-m['B']/m['w'])*tau
            elif m['s']<3:approx=m['kappa']*mp.gamma(1-m['s'])/m['B']*tau**(m['s']-1)
            elif m['s']>3:approx=(1+m['kappa']*mp.zeta(m['s']-2)+m['prefix'])/(2*m['B'])*tau*tau
            else:
                K=m['B']/m['kappa'];b0=mp.mpf('1.5')+(1+m['prefix'])/m['kappa']
                approx=tau*tau/(2*K)*(mp.log(1/tau)+b0)
                Y=-mp.lambertw(-4*K*mp.exp(-2*b0)*X,-1);tau0=2*mp.sqrt(K*X/Y)
                eq=tau0*tau0/(2*K)*(mp.log(1/tau0)+b0)-X;assert abs(eq)<mp.mpf('1e-70')
                identities.append({'s':ss,'kappa':kap,'prefix':pre,'tau':mp.nstr(tau,8),
                  'lambert_exact_residual':mp.nstr(abs(eq),8),'(tau-tau0)/tau0^2':mp.nstr((tau-tau0)/tau0**2,22)})
            rows.append({'s':ss,'critical':crit,'kappa':kap,'prefix':pre,'tau':mp.nstr(tau,8),
              'X/leading_local':mp.nstr(X/approx,24),'original_equation_residual':mp.nstr(abs(resid),8)})
    for ss in ('2.5','3','4'):
        m=model(ss)
        for angle in (mp.mpf('0.7'),mp.mpf('-1.2')):
            tau=mp.mpf('0.00001')*mp.exp(1j*angle)
            X=tau-(mp.sqrt(m['u']**2-2*f(m,mp.exp(-tau)))-m['w'])
            v=m['vb']+X-tau;r=m['R']*mp.exp(-X)
            resid=m['u']*v-v*v/2-f(m,r*mp.exp(v));assert abs(resid)<mp.mpf('1e-70')
            rows.append({'s':ss,'critical':True,'kappa':'1','prefix':'0','tau':mp.nstr(tau,8),
              'X/leading_local':'complex identity','original_equation_residual':mp.nstr(abs(resid),8)})
    write_csv(out/'local_checks.csv',rows);write_csv(out/'lambert_checks.csv',identities)
    return {'precision_decimal_digits':mp.mp.dps,'original_equation_checks':len(rows),
      'lambert_core_identity_checks':len(identities),
      'largest_absolute_original_residual':str(max(mp.mpf(x['original_equation_residual']) for x in rows)),
      'scope':'Floating-point identities, not interval or global-continuation certificates.'}


def coefficient_checks(out: Path, max_n: int) -> dict:
    models=[model('2.5'),model('3'),model('4'),model('2.5',False),model('3',False),
            model('4',False),model('3',True,'2','0.5')]
    targets=sorted(set([n for n in (64,128,256,512,1024,2048,4096,8192) if n<=max_n]+[max_n]))
    rows=[];cross=[];constants=[]
    for m in models:
        tag=f"s={m['s']} critical={m['critical']} kappa={m['kappa']} prefix={m['prefix']}"
        print(tag,flush=True);h=numerical_lift(m,max_n);ref=probability_mp(m,32)
        try:
            value=mp.mpf(str(probability_ld(h,m['vb'],32)));err=abs(value/ref-1);assert err<mp.mpf('1e-12')
            cross.append({'model':tag,'n':32,'relative_error':mp.nstr(err,12)})
        except FloatingPointError:cross.append({'model':tag,'n':32,'relative_error':'longdouble unavailable'})
        constants.append({'model':tag,**{k:mp.nstr(m[k],50) for k in ('A','B','w','u','vb','R')}})
        for n in targets:
            try:value=mp.mpf(str(probability_ld(h,m['vb'],n)));engine='numpy.longdouble'
            except FloatingPointError:value=probability_mp(m,n);engine='mpmath fallback'
            lead,first,second=asymptotics(m,n)
            rows.append({'s':str(m['s']),'critical':m['critical'],'kappa':str(m['kappa']),
              'prefix':str(m['prefix']),'n':n,'a_n_R^n':mp.nstr(value,22),
              'ratio_to_leading':mp.nstr(value/lead,16),'ratio_to_first_refinement':mp.nstr(value/first,16),
              'ratio_to_second_refinement':mp.nstr(value/second,16),'engine':engine})
    write_csv(out/'coefficient_diagnostics.csv',rows);write_csv(out/'precision_crosschecks.csv',cross)
    (out/'model_constants.json').write_text(json.dumps(constants,indent=2)+'\n')
    return {'models':len(models),'coefficient_evaluations':len(rows),'max_n':max_n,
      'longdouble_decimal_precision':int(np.finfo(np.longdouble).precision),
      'scope':'Positive recurrence in floating-point arithmetic; asymptotic ratios are diagnostics, not proofs.'}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,default=Path('replay'))
    ap.add_argument('--max-n',type=int,default=4096);args=ap.parse_args()
    if not 64<=args.max_n<=8192:ap.error('--max-n must be in [64,8192]')
    if args.output_dir.exists() and any(args.output_dir.iterdir()):ap.error('Choose an absent or empty output directory.')
    args.output_dir.mkdir(parents=True,exist_ok=True);mp.mp.dps=85
    result={'python':sys.version,'platform':platform.platform(),'sympy':sp.__version__,
      'mpmath':mp.__version__,'numpy':np.__version__,
      'evidence_status':'Exact finite checks plus non-certified floating-point diagnostics; not Lean or interval verification.'}
    print('Exact comparisons',flush=True);result['exact']=exact_checks(args.output_dir)
    print('Local coordinate diagnostics',flush=True);result['local']=local_checks(args.output_dir)
    print('Coefficient diagnostics',flush=True);result['coefficients']=coefficient_checks(args.output_dir,args.max_n)
    (args.output_dir/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
