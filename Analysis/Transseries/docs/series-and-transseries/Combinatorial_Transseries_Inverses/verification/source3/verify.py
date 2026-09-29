#!/usr/bin/env python3
"""Reproduce checks and numerical tables for the accompanying article.

Requires Python >=3.9 and mpmath. No network access is used.
Run: python verify.py --output verification_report.json
All arithmetic sequence checks use Python integers. Analytic checks use
mpmath at 110 decimal digits; these checks complement, not replace, proofs.
"""
from __future__ import annotations
import argparse
import json
import math
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Callable, List
import mpmath as mp

mp.mp.dps = 110
M = mp.mpf


def exp_series(g: List[mp.mpf], degree: int) -> List[mp.mpf]:
    """Coefficients of exp(g(t)), using k f_k=sum j g_j f_(k-j)."""
    f = [mp.exp(g[0])] + [M(0)] * degree
    for k in range(1, degree + 1):
        f[k] = mp.fsum(j*g[j]*f[k-j] for j in range(1, min(k, len(g)-1)+1))/k
    return f


def log_series(f: List[mp.mpf], degree: int) -> List[mp.mpf]:
    """Coefficients of log(f); requires f[0]>0 in these applications."""
    g = [mp.log(f[0])] + [M(0)]*degree
    for n in range(1, degree+1):
        g[n] = (n*f[n]-mp.fsum(k*g[k]*f[n-k] for k in range(1,n)))/(n*f[0])
    return g


def inverse_coefficients(a, lam, D, b, degree):
    """Solve D*d+a*d^2+B(t exp(-lam*d))=0, coefficient by coefficient."""
    d = [M(0)]*(degree+1)
    for n in range(1, degree+1):
        rhs = a*mp.fsum(d[j]*d[n-j] for j in range(1,n))
        for k in range(1,n+1):
            e = exp_series([-k*lam*v for v in d[:n-k+1]], n-k)
            rhs += b[k]*e[n-k]
        d[n] = -rhs/D
    return d


def poly_value(c, t):
    return mp.polyval(list(reversed(c)),t)


@lru_cache(None)
def log_p(Qstr: str):
    """log((Q;Q)_infinity), absolute tail below 10^(-dps-10)."""
    Q=M(Qstr)
    J=int(mp.ceil((mp.mp.dps+15)*mp.log(10)/(-mp.log(Q))))+10
    return mp.fsum(mp.log1p(-Q**j) for j in range(1,J+1))


def A(Q,t):
    """-log((Q*t;Q)_infinity), for |Q*t|<1."""
    if abs(Q*t)>=1:
        raise ValueError('A requires |Q*t| < 1')
    if not t:
        return M(0)
    z=Q*t
    K=max(20,int(mp.ceil((mp.mp.dps+15)*mp.log(10)/(-mp.log(abs(z)))))+5)
    return mp.fsum(z**k/(k*(1-Q**k)) for k in range(1,K+1))


def ac(Q,k):
    return Q**k/(k*(1-Q**k))


@dataclass
class Model:
    name: str
    a: mp.mpf
    b: mp.mpf
    c: mp.mpf
    lam: mp.mpf
    coeff: Callable[[int],mp.mpf]
    tail: Callable[[mp.mpf],mp.mpf]

    def log_value(self,x):
        return self.a*x*x+self.b*x+self.c+self.tail(mp.exp(-self.lam*x))

    def center(self,L):
        return ((L-self.c)/self.b if not self.a else
                (-self.b+mp.sqrt(self.b*self.b+4*self.a*(L-self.c)))/(2*self.a))

    def invert(self,L,degree):
        s=self.center(L)
        D=2*self.a*s+self.b
        cs=[M(0)]+[self.coeff(k) for k in range(1,degree+1)]
        ds=inverse_coefficients(self.a,self.lam,D,cs,degree)
        return s+poly_value(ds,mp.exp(-self.lam*s))


def make_models(q=2):
    q=M(q); Q=1/q; h=mp.log(q); lp=log_p(str(Q))
    aa=lambda k: ac(Q,k)
    out={}
    out['GL']=Model('GL',h,M(0),lp,h,aa,lambda t:A(Q,t))
    out['Grassmann']=Model('Grassmann',h,M(0),-lp,h,
        lambda k:-2*aa(k)+(aa(k//2) if k%2==0 else 0),
        lambda t:A(Q,t*t)-2*A(Q,t))
    out['Complete flags']=Model('Complete flags',h/2,h/2-mp.log(q-1),lp,h,
        aa,lambda t:A(Q,t))
    out['q-Catalan']=Model('q-Catalan',h,-h,mp.log(1-Q)-lp,h,
        lambda k:-2*aa(k)+(aa(k//2) if k%2==0 else 0)+Q**k/k,
        lambda t:A(Q,t*t)-2*A(Q,t)-mp.log1p(-Q*t))
    out['Symplectic']=Model('Symplectic',2*h,h,log_p(str(Q*Q)),h,
        lambda k:ac(Q*Q,k//2) if k%2==0 else M(0),lambda t:A(Q*Q,t*t))
    lpminus=mp.fsum(mp.log(1-(-Q)**j) for j in range(1,450))
    for eps in (0,1):
        def coef(k,eps=eps):
            return (-1)**(k*(eps+1))*Q**k/(k*(1-(-Q)**k))
        def tail(t,eps=eps):
            return mp.fsum((-1)**(k*(eps+1))*(Q*t)**k/(k*(1-(-Q)**k))
                           for k in range(1,450))
        out[f'Unitary {eps}']=Model(f'Unitary {eps}',h,M(0),lpminus,h,coef,tail)
    return out


@lru_cache(None)
def qbin(n,k,q=2):
    if k<0 or k>n:
        return 0
    if k==0 or k==n:
        return 1
    # Both factors are exact integers; this form needs no rational arithmetic.
    return qbin(n-1,k-1,q)+q**k*qbin(n-1,k,q)


@lru_cache(None)
def galois(n,r=2,q=2):
    if r==1:
        return 1
    return sum(qbin(n,k,q)*galois(n-k,r-1,q) for k in range(n+1))


@lru_cache(None)
def theta(eps,r,Qstr='0.5'):
    """Root-lattice theta constants for r=2 or 3; tails negligible here.

    Range -34..34 gives > 110-digit accuracy at Q=1/2 for r<=3.
    The finite theta computation is used only for numerical checks.
    """
    Q=M(Qstr); eps%=r
    if r==2:
        return mp.fsum(Q**((M(j)-M(eps)/2)**2) for j in range(-34,35))
    if r==3:
        e=M(eps)/3
        return mp.fsum(Q**(((M(i)-e)**2+(M(j)-e)**2+(M(eps-i-j)-e)**2)/2)
                       for i in range(-34,35) for j in range(-34,35))
    raise ValueError('The numerical theta implementation supports r=2 or 3.')


def galois_H_coeffs(r,eps,degree,Q=M('.5')):
    """Entire theta-tail coefficients, formula (root-lattice theorem)."""
    p=[M(1)]
    for k in range(1,degree+1): p.append(p[-1]*(1-Q**k))
    comp=[M(1)]+[M(0)]*degree
    for _ in range(r):
        comp=[mp.fsum(comp[j]/p[k-j] for j in range(k+1)) for k in range(degree+1)]
    return [(-1)**k * Q**(M(k*k)/(2*r)+M(k)/2)*theta((eps+k)%r,r,str(Q))*comp[k]
            for k in range(degree+1)]


def galois_model(r,eps,degree=65):
    Q=M('.5'); h=mp.log(2)
    cs=galois_H_coeffs(r,eps,degree,Q)
    bc=log_series(cs,degree)
    for k in range(r,degree+1,r): bc[k]+=ac(Q,k//r)
    c=mp.log(cs[0])-(r-1)*log_p(str(Q))
    return Model(f'Galois r={r}, eps={eps}',h*(r-1)/(2*r),M(0),c,h/r,
                 lambda k:bc[k],lambda t:A(Q,t**r)+mp.log(poly_value(cs,t)/cs[0]))


def mobius(n):
    sign=1; p=2
    while p*p<=n:
        if n%p==0:
            n//=p; sign=-sign
            if n%p==0: return 0
            while n%p==0: n//=p
        p+=1
    return -sign if n>1 else sign


def irreducibles(n,q=2):
    return sum(mobius(d)*q**(n//d) for d in range(1,n+1) if n%d==0)//n


def sci(x,digits=8):
    return mp.nstr(x,digits,min_fixed=0,max_fixed=0)



def poly_mul(a,b,degree):
    return [mp.fsum(a[j]*b[k-j] for j in range(max(0,k-len(b)+1),min(k,len(a)-1)+1))
            for k in range(degree+1)]


def poly_power(a,k,degree):
    out=[M(1)]+[M(0)]*degree
    for _ in range(k): out=poly_mul(out,a,degree)
    return out


def reciprocal_series(a,degree):
    out=[1/a[0]]+[M(0)]*degree
    for n in range(1,degree+1):
        out[n]=-mp.fsum(a[j]*out[n-j] for j in range(1,min(n,len(a)-1)+1))/a[0]
    return out


def finite_inverse_coeff(a,lam,D,b,m):
    """The article's nonrecursive finite composition/binomial formula."""
    ans=M(0)
    for k in range(1,m+1):
        C=poly_power(b,k,m)[m]
        ans-=C/k*mp.fsum(math.comb(k+j-1,j)*a**j*(m*lam)**(k-1-j)
                         /(math.factorial(k-1-j)*D**(k+j)) for j in range(k))
    return ans


def inverse_logphase_coeff(h,kappa,s,b,degree):
    """Inverse coefficients for P(x)=h*x-log(x), not a quadratic phase."""
    D=h-1/s; d=[M(0)]*(degree+1)
    for n in range(1,degree+1):
        residual=mp.fsum((-1)**j*poly_power(d,j,n)[n]/(j*s**j) for j in range(2,n+1))
        residual+=mp.fsum(b[k]*exp_series([-k*kappa*v for v in d[:n-k+1]],n-k)[n-k]
                           for k in range(1,n+1))
        d[n]=-residual/D
    return d


def supplemental_checks():
    checks=0; rows=[]
    # The finite formula and the independent recurrence agree through weight 8.
    bc=[M(0)]+[M((-1)**k*(k+2))/M(k+1) for k in range(1,9)]
    for a in (M(0),M(3)/7):
        D=M(17)/3; lam=M(5)/11
        dc=inverse_coefficients(a,lam,D,bc,8)
        for n in range(1,9):
            assert abs(dc[n]-finite_inverse_coeff(a,lam,D,bc,n))<M('1e-95')
            checks+=1
    # Linear phases: fixed rank and small-base q-factorials.
    h=mp.log(2); Q=M('.5'); lp=log_p('.5'); k=3
    pk=mp.fprod(1-Q**j for j in range(1,k+1))
    fixed=Model('Fixed rank k=3',M(0),k*h,-h*k*k-mp.log(pk),h,
                lambda m:-(M(2)**(k*m)-1)/(m*(M(2)**m-1)),
                lambda t:mp.fsum(mp.log1p(-M(2)**j*t) for j in range(k)))
    small=Model('q-factorial base 1/2',M(0),h,lp,h,lambda m:ac(Q,m),lambda t:A(Q,t))
    for n in range(3,13):
        assert abs(mp.exp(fixed.log_value(n))/qbin(n,k)-1)<M('1e-90')
        checks+=1
    for model in (fixed,small):
        x=M('12.25'); L=model.log_value(x)
        row={'family':model.name,'x':str(x),'logY':sci(L,30),'s':sci(model.center(L),30)}
        row['errors']={str(d):sci(abs(model.invert(L,d)-x)) for d in (0,1,2,4,6,8)}
        rows.append(row)
    # Nonquadratic Lambert-W center, on two fixed-radical sheets.
    for label,E,kappa,x in [
        ('Prime-power index p=2',[M(1),M(-1)],h/2,M('16.25')),
        ('Fixed radical R=6',[M(1),M(0),M(0),M(-1),M(-1),M(1)],h/6,M('36.25'))]:
        bc=log_series(E+[M(0)]*(9-len(E)),8)
        L=h*x-mp.log(x)+mp.log(poly_value(E,mp.exp(-kappa*x)))
        ss=-mp.lambertw(-h*mp.exp(-L),-1)/h
        ds=inverse_logphase_coeff(h,kappa,ss,bc,8)
        t=mp.exp(-kappa*ss); D=h-1/ss
        for n in range(1,9):
            residual=D*ds[n]+mp.fsum((-1)**j*poly_power(ds,j,n)[n]/(j*ss**j) for j in range(2,n+1))
            residual+=mp.fsum(bc[k]*exp_series([-k*kappa*v for v in ds[:n-k+1]],n-k)[n-k]
                              for k in range(1,n+1))
            assert abs(residual)<M('1e-95')
            checks+=1
        if len(E)==2:
            d2=1/(2*D)-kappa/D**2-1/(2*ss**2*D**3)
            assert abs(ds[1]-1/D)<M('1e-95') and abs(ds[2]-d2)<M('1e-95')
            checks+=1
        row={'family':label,'x':str(x),'logY':sci(L,30),'s':sci(ss,30)}
        row['errors']={str(d):sci(abs(ss+poly_value(ds[:d+1],t)-x)) for d in (0,1,2,4,6,8)}
        rows.append(row)
    # Weighted theta identity for the Rogers-Szego polynomial at z=3.
    z=M(3); degree=65; pp=[M(1)]
    for j in range(1,degree+1):pp.append(pp[-1]*(1-Q**j))
    th=[mp.fsum(Q**((M(j)+M(e)/2)**2)*z**(M(j)+M(e)/2) for j in range(-34,35))
        for e in (0,1)]
    for eps in (0,1):
        cs=[(-1)**m*Q**(M(m*m)/4+M(m)/2)*th[(eps+m)%2]
            *mp.fsum(z**(M(m)/2-j)/(pp[j]*pp[m-j]) for j in range(m+1))
            for m in range(degree+1)]
        for n in range(eps,13,2):
            t=Q**(M(n)/2)
            approx=mp.exp(-lp+h*n*n/4+M(n)*mp.log(z)/2+A(Q,t*t))*poly_value(cs,t)
            exact=sum(qbin(n,k)*3**k for k in range(n+1))
            assert abs(approx/exact-1)<M('1e-85'),('weighted',n)
            checks+=1
    # Endpoint inverse, from the independent Lagrange coefficient formula.
    degree=8; acs=[ac(Q,j+1) for j in range(degree+1)]
    R=reciprocal_series(acs,degree)
    es=[M(0)]+[-poly_power(R,m,m)[m]/(m*h) for m in range(1,degree+1)]
    xx=M('16.25'); eps=A(Q,Q**xx); x0=mp.log(acs[0]/eps)/h
    endpoint={'x':str(xx),'epsilon':sci(eps,30),
              'errors':{str(d):sci(abs(x0+poly_value(es[:d+1],eps)-xx)) for d in (0,1,2,4,6,8)}}
    assert abs(x0+poly_value(es,eps)-xx)<eps**8
    assert abs(es[1]-1/(6*h))<M('1e-95')
    assert abs(es[2]-1/(168*h))<M('1e-95')
    checks+=3
    return checks,rows,endpoint


def run_checks():
    checks=0
    models=make_models()
    # Independent small integer values from the linked OEIS definitions.
    expected={
        'GL':[1,1,6,168,20160],
        'Grassmann':[1,3,35,1395,200787],
        'q-Catalan':[1,1,5,93,6477],
        'Complete flags':[1,1,3,21,315],
        'Symplectic':[1,6,720,1451520],
    }
    for name,seq in expected.items():
        for n,v in enumerate(seq):
            assert abs(mp.exp(models[name].log_value(n))-v)<M('1e-90')*max(1,v),(name,n)
            checks+=1
    for n,v in enumerate([3,18,648,77760,41057280],1):
        assert abs(mp.exp(models[f'Unitary {n%2}'].log_value(n))-v)<M('1e-90')*v
        checks+=1
    assert [galois(n) for n in range(8)]==[1,2,5,16,67,374,2825,29212]
    checks+=1
    # Entire theta-tail interpolation agrees with the exact flag count.
    gm={}
    for r in (2,3):
        for eps in range(r):
            model=galois_model(r,eps)
            gm[(r,eps)]=model
            for n in range(eps,17,r):
                value=mp.exp(model.log_value(n)); exact=galois(n,r)
                assert abs(value/exact-1)<M('1e-85'),('theta',r,n,sci(value/exact-1))
                checks+=1
    # Numeric coefficient identities tested by power-series substitution.
    for name,model in {**models,**{m.name:m for m in gm.values()}}.items():
        s=M('9.25'); D=2*model.a*s+model.b; K=8
        bc=[M(0)]+[model.coeff(k) for k in range(1,K+1)]
        dc=inverse_coefficients(model.a,model.lam,D,bc,K)
        for n in range(1,K+1):
            residual=D*dc[n]+model.a*mp.fsum(dc[j]*dc[n-j] for j in range(1,n))
            residual+=mp.fsum(bc[k]*exp_series([-k*model.lam*v for v in dc[:n-k+1]],n-k)[n-k]
                               for k in range(1,n+1))
            assert abs(residual)<M('1e-95'),(name,n)
            checks+=1
        b1,b2,b3=bc[1:4]; a=model.a; lam=model.lam
        assert abs(dc[1]+b1/D)<M('1e-95')
        assert abs(dc[2]+b2/D+lam*b1*b1/D**2+a*b1*b1/D**3)<M('1e-95')
        d3=-(b3/D+3*lam*b1*b2/D**2+(2*a*b1*b2+M('1.5')*lam**2*b1**3)/D**3
              +3*a*lam*b1**3/D**4+2*a*a*b1**3/D**5)
        assert abs(dc[3]-d3)<M('1e-95')
        checks+=3
    for n in range(1,151):
        I=irreducibles(n)
        deficit=2**n-n*I
        assert 0<=deficit<=2**(n//2+1)-2
        checks+=1
    assert [irreducibles(n) for n in range(1,11)]==[2,1,2,3,6,9,18,30,56,99]
    checks+=1
    # The two-candidate threshold criterion is checked without Lambert-W
    # rounding issues: targets are rational points in (B(n-1),B(n)].
    from fractions import Fraction as F
    for q in (2,3,5):
        for n0 in range(4,61):
            lo=F(q**(n0-1),n0-1); hi=F(q**n0,n0)
            for p in (F(1,100),F(1,2),F(99,100),F(1,1)):
                Y=lo+p*(hi-lo)
                predicted=n0 if irreducibles(n0,q)>=Y else n0+1
                actual=next(n for n in range(1,n0+2) if irreducibles(n,q)>=Y)
                assert predicted==actual,(q,n0,p)
                checks+=1
    rows=[]
    for name,x in [('GL','8.25'),('Grassmann','8.25'),('q-Catalan','8.25'),
                   ('Symplectic','8.25'),('Unitary 0','8.25'),('Unitary 1','8.25')]:
        model=models[name]; xx=M(x); L=model.log_value(xx)
        row={'family':name,'x':x,'logY':sci(L,30),'s':sci(model.center(L),30)}
        row['errors']={str(k):sci(abs(model.invert(L,k)-xx)) for k in (0,1,2,4,6,8)}
        rows.append(row)
    for r,eps,x in [(2,0,'16.25'),(2,1,'17.25'),(3,0,'18.25')]:
        model=gm[(r,eps)]; xx=M(x); L=model.log_value(xx)
        row={'family':model.name,'x':x,'logY':sci(L,30),'s':sci(model.center(L),30)}
        row['errors']={str(k):sci(abs(model.invert(L,k)-xx)) for k in (0,1,2,4,6,8)}
        rows.append(row)
    # q -> 1 entropy transition: compare a truncated EM expression with exact.
    transition=[]
    for hstr in ('.2','.1','.05'):
        h=M(hstr); Q=mp.exp(-h); tau=M(1); t=mp.exp(-tau)
        exact=tau*tau/h-log_p(str(Q))+A(Q,t*t)-2*A(Q,t)
        S=tau*tau+mp.pi**2/6+mp.polylog(2,t*t)-2*mp.polylog(2,t)
        amp=mp.log(1-t*t)/2-mp.log(1-t)
        E1=-M(1)/24+(mp.polylog(0,t*t)-2*mp.polylog(0,t))/12
        E3=-(mp.polylog(-2,t*t)-2*mp.polylog(-2,t))/720
        approx=S/h-mp.log(2*mp.pi/h)/2+amp+h*E1+h**3*E3
        transition.append({'h':hstr,'exact_log':sci(exact,25),'error_through_h3':sci(abs(exact-approx))})
    more,extra,endpoint=supplemental_checks()
    checks+=more; rows.extend(extra)
    return {'endpoint':endpoint,'precision_digits':mp.mp.dps,'checks_passed':checks,'inverse_tables':rows,
            'theta_constants':{f'r{r}_eps{e}':sci(theta(e,r),35) for r in (2,3) for e in range(r)},
            'P_half':sci(mp.exp(log_p('.5')),40),
            'P_minus_half':sci(mp.exp(models['Unitary 0'].c),40),
            'double_scaling':transition}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('verification_report.json'))
    args=parser.parse_args()
    report=run_checks()
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f"Passed {report['checks_passed']} checks at {report['precision_digits']} decimal digits.")
    print(f'Report: {args.output}')
    for row in report['inverse_tables']:
        print(row['family'],row['errors'])
