#!/usr/bin/env python3
"""Reproduce exact checks and asymptotic tables for matrix_compositions.tex.

Requires Python >=3.10, sympy and mpmath. No network access is used.
Run from any directory: python scripts/verify.py --max-m 200
Numerical checks support, but do not replace, the proofs in the article.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import sys
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DIAGONAL_FIXTURE = [
    1, 2, 66, 5546, 893490, 235804122, 92540869002,
    50592275219138, 36763980389367378, 34277110454602760762,
    39890088439337327537706, 56678337951284473917309346,
    96562013312452672907356749786,
    194303876852797223949281552591106,
    455927121076167354458618221923117282,
]
TRIANGLE_FIXTURE = [
    [1], [0,1], [0,2,3], [0,4,16,13], [0,8,66,132,75],
    [0,16,248,924,1232,541], [0,32,892,5546,13064,13060,4683],
    [0,64,3136,30720,114032,195020,155928,47293],
]
# Finite data transcribed from OEIS A261781 and A261784, retrieved 2026-10-03.

def stirling_tables(N: int) -> tuple[list[list[int]], list[list[int]]]:
    first, second = [[1]], [[1]]
    for n in range(1,N+1):
        a,b=[0]*(n+1),[0]*(n+1)
        for j in range(1,n+1):
            a[j]=first[-1][j-1]+((n-1)*first[-1][j] if j<n else 0)
            b[j]=second[-1][j-1]+(j*second[-1][j] if j<n else 0)
        first.append(a); second.append(b)
    return first,second

def unrestricted(N: int, k: int) -> list[int]:
    """U(n,k) from the rational ordinary generating function, exactly."""
    out=[1]+[0]*N
    if k==0: return out
    q=[1]+[2*(-1)**j*math.comb(k,j) for j in range(1,k+1)]
    for n in range(1,N+1):
        numerator=(-1)**n*math.comb(k,n) if n<=k else 0
        out[n]=numerator-sum(q[j]*out[n-j] for j in range(1,min(k,n)+1))
    return out

def kernel_polynomials(M: int = 3) -> list[sp.Expr]:
    n,h,v,a=sp.symbols('n h v a')
    e=[sp.Integer(1)]
    w=[]
    for ell in range(2*M+1):
        if ell:
            e.append(sp.factor(sum((-1)**(j-1)*e[ell-j]*
                 sp.summation(a**j,(a,1,n-1)) for j in range(1,ell+1))/ell))
        den=sp.prod(n-j for j in range(ell))**2
        w.append(sp.series((e[ell]/den).subs(n,1/h),h,0,M+1).removeO().expand())
    p=[]
    for r in range(M+1):
        p.append(sp.expand(sum(v**m*sum((-sp.Rational(1,2))**(m-ell)/
            sp.factorial(m-ell)*w[ell].coeff(h,r) for ell in range(m+1))
            for m in range(2*r+1))))
    assert sp.expand(p[1]-v*(v-6)/12)==0
    assert sp.expand(p[2]-v**2*(v**2-24)/288)==0
    return p

def cumulant_polynomials(J: int) -> list[sp.Expr]:
    z,a=sp.symbols('z a')
    out=[sp.Integer(0),a]
    for j in range(1,J):
        out.append(sp.expand(z*sp.diff(out[-1],z)+
                    a*(1+z-a)*sp.diff(out[-1],a)))
    return out

def poly_add(a: dict[int,mp.mpf], b: dict[int,mp.mpf], scale=1):
    out=a.copy()
    for j,x in b.items(): out[j]=out.get(j,mp.mpf(0))+scale*x
    return out

def poly_mul(a: dict[int,mp.mpf], b: dict[int,mp.mpf]):
    out={}
    for i,x in a.items():
        for j,y in b.items(): out[i+j]=out.get(i+j,mp.mpf(0))+x*y
    return out

def saddle_coefficients(rho: mp.mpf, tau: mp.mpf, M: int,
                        ps: list[sp.Expr]) -> list[mp.mpf]:
    """Finite formal Gaussian algorithm, no numerical quadrature."""
    L=mp.log(2); mu=L*tau/2; H=2*M
    z,a,v=sp.symbols('z a v')
    ks=cumulant_polynomials(H+2)
    kap=[mp.mpf(0)]+[sp.lambdify((z,a),ks[j],'mpmath')(tau,rho)
                       for j in range(1,H+3)]
    b=kap[2]
    exponent=[{} for _ in range(H+1)]
    for j in range(1,H+1):
        exponent[j]=poly_add(exponent[j],{j:mu/mp.factorial(j)})
    for j in range(3,H+3):
        exponent[j-2]=poly_add(exponent[j-2],{j:kap[j]/mp.factorial(j)})
    ee=[{0:mp.mpf(1)}]
    for n in range(1,H+1):
        val={}
        for j in range(1,n+1):
            val=poly_add(val,poly_mul(exponent[j],ee[n-j]),mp.mpf(j)/n)
        ee.append(val)
    kernel=[{} for _ in range(H+1)]
    for r in range(M+1):
        for (d,),c in sp.Poly(ps[r],v).terms():
            cc=mp.mpf(str(c.p))/int(c.q)*(L*tau)**d/rho**r
            for j in range(H-2*r+1):
                kernel[2*r+j]=poly_add(kernel[2*r+j],
                    {j:cc*mp.mpf(d)**j/mp.factorial(j)})
    result=[]
    for n in range(H+1):
        coeff={}
        for j in range(n+1): coeff=poly_add(coeff,poly_mul(ee[j],kernel[n-j]))
        val=mp.mpf(0)
        for j,x in coeff.items():
            if j%2==0:
                t=j//2
                moment=(-1)**t*mp.factorial(2*t)/(2**t*mp.factorial(t)*b**t)
                val+=x*moment
        if n%2==0: result.append(val)
        else: assert abs(val)<mp.mpf('1e-65')
    a1=kap[4]/(8*b*b)-5*kap[3]**2/(24*b**3)-(mu*mu+mu)/(2*b)+\
       kap[3]*mu/(2*b*b)+(mu*mu/3-mu)/rho
    assert abs(result[0]-1)<mp.mpf('1e-65')
    assert abs(result[1]-a1)<mp.mpf('1e-60')
    return result

def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

def run(max_m: int) -> None:
    if max_m<14: raise ValueError('--max-m must be at least 14')
    mp.mp.dps=90
    start=time.monotonic()
    N=2*max_m
    first,second=stirling_tables(N)
    fac=[math.factorial(n) for n in range(N+1)]
    F=[sum(fac[j]*second[n][j] for j in range(n+1)) for n in range(N+1)]
    def T(n:int,k:int)->int:
        if k>n: return 0
        S=sum(first[n][j]*second[j][k]*F[j] for j in range(k,n+1))
        num=fac[k]*S
        assert num%fac[n]==0
        return num//fac[n]
    for n,row in enumerate(TRIANGLE_FIXTURE):
        assert [T(n,k) for k in range(n+1)]==row
    diagonals=[T(2*m,m) for m in range(max_m+1)]
    assert diagonals[:len(DIAGONAL_FIXTURE)]==DIAGONAL_FIXTURE
    # Independent rational-GF and inclusion-exclusion calculation.
    checkN=min(40,N)
    Us=[unrestricted(checkN,k) for k in range(checkN+1)]
    for n in range(checkN+1):
        for k in range(n+1):
            ie=sum((-1)**(k-j)*math.comb(k,j)*Us[j][n] for j in range(k+1))
            assert ie==T(n,k),(n,k,ie,T(n,k))
    # Independently verify denominator coprimality and recurrence.
    zz=sp.symbols('z'); denom_checks=[]
    for k in range(1,9):
        D=sp.Poly(sp.prod(2*(1-zz)**j-1 for j in range(1,k+1)),zz)
        Tk=sum((-1)**(k-j)*math.comb(k,j)*
               ((1-zz)**j/(2*(1-zz)**j-1) if j else 1)
               for j in range(k+1))
        num,den=sp.fraction(sp.cancel(Tk))
        assert sp.degree(den,zz)==k*(k+1)//2
        assert sp.degree(sp.gcd(sp.Poly(num,zz),D))==0
        degree=D.degree(); dc=[int(D.nth(j)) for j in range(degree+1)]
        vals=[T(n,k) for n in range(min(N,degree+8)+1)]
        for n in range(degree+1,len(vals)):
            assert sum(dc[j]*vals[n-j] for j in range(degree+1))==0
        denom_checks.append({'k':k,'degree':degree,'D':str(D.as_expr())})
    # Exact finite-kernel differential recurrence, all coefficients.
    for n in range(1,min(80,N-1)+1):
        def w(NN,ll):
            if ll<0 or ll>=NN: return sp.Rational(0)
            return sp.Rational(first[NN][NN-ll],(fac[NN]//fac[NN-ll])**2)
        for ell in range(n+1):
            assert (n+1)**2*w(n+1,ell)==(n+1-ell)**2*w(n,ell)+n*w(n,ell-1)
    ps=kernel_polynomials(3)
    L=mp.log(2); tau=2+mp.lambertw(-2*mp.e**-2,0)
    rho=mp.mpf(2); b=2*(tau-1); mu=L*tau/2
    d=4/(L**2*tau*(2-tau)); c=mp.exp(mu)/(4*mp.pi*L*mp.sqrt(tau-1))
    As=saddle_coefficients(rho,tau,3,ps)
    cb=[mp.mpf(1),-mp.mpf(1)/8,mp.mpf(1)/128,mp.mpf(5)/1024]
    ds=[sum(As[j]*cb[r-j] for j in range(r+1)) for r in range(4)]
    rows=[]
    for m in [5,10,20,30,50,75,100,150,200,300,500]:
        if m>max_m: continue
        exact=mp.mpf(diagonals[m]); leading=c*d**m*mp.factorial(m)**2/m
        ratio=exact/leading
        row={'m':m,'a_over_leading':mp.nstr(ratio,24)}
        for order in range(4):
            approx=sum(ds[j]/mp.mpf(m)**j for j in range(order+1))
            row[f'relative_error_order_{order}']=mp.nstr(approx/ratio-1,18)
        rows.append(row)
    defect=[]
    for m in [10,20,50,100,200]:
        if m>max_m: continue
        n=2*m; den=sum(first[n][j]*second[j][m]*F[j] for j in range(m,n+1))
        for ell in range(7):
            p=mp.mpf(first[n][n-ell]*second[n-ell][m]*F[n-ell])/den
            pois=mp.exp(-mu)*mu**ell/mp.factorial(ell)
            defect.append({'m':m,'defect':ell,'probability':mp.nstr(p,20),
                           'Poisson_limit':mp.nstr(pois,20)})
    coupon=[]
    # Exact integers, computed directly with rational generating functions.
    for k in [10,20,40,80,120]:
        for s in [-1,0,1]:
            n=int(mp.nint(k*(mp.log(k)+s)))
            if n<k: continue
            UU=[unrestricted(n,j)[n] for j in range(k+1)]
            tt=sum((-1)**(k-j)*math.comb(k,j)*UU[j] for j in range(k+1))
            p=mp.mpf(tt)/UU[k]; hh=mp.mpf(n)/k
            lam=k*mp.exp(-hh)
            lead=mp.exp(-lam)
            corr=lead*(1+((1-L)*hh*lam-(hh+1)*lam**2)/(2*k))
            coupon.append({'k':k,'n':n,'s_actual':mp.nstr(hh-mp.log(k),14),
               'probability_exact':mp.nstr(p,20),'Poisson_approximation':mp.nstr(lead,20),
               'corrected_approximation':mp.nstr(corr,20),
               'error_leading':mp.nstr(lead-p,14),'error_corrected':mp.nstr(corr-p,14)})
    out=ROOT/'results'; out.mkdir(exist_ok=True)
    write_csv(out/'a261784_asymptotics.csv',rows)
    write_csv(out/'coupon_transition.csv',coupon)
    write_csv(out/'stirling_defect.csv',defect)
    with (out/'a261784_exact.txt').open('w') as f:
        f.write('# Computed exactly by the published Stirling/Fubini identity.\n')
        for m,x in enumerate(diagonals): f.write(f'{m} {x}\n')
    constants={'L':L,'tau':tau,'b':b,'mu':mu,'d':d,'c':c,
               **{f'A{j}':As[j] for j in range(1,4)},
               **{f'delta{j}':ds[j] for j in range(1,4)},'beta1':ds[1]+mp.mpf(1)/6}
    report={'status':'ALL CHECKS PASSED','max_m':max_m,
       'triangle_fixture_rows':len(TRIANGLE_FIXTURE),'diagonal_fixture_terms':len(DIAGONAL_FIXTURE),
       'independent_GF_IE_triangle_through_n':checkN,
       'reduced_denominators_checked_through_k':8,
       'kernel_recurrence_checked_through_n':min(80,N-1),
       'kernel_polynomials':[str(p) for p in ps],
       'constants':{k:mp.nstr(x,70) for k,x in constants.items()},
       'denominator_checks':denom_checks,
       'precision_decimal_digits':mp.mp.dps,
       'elapsed_seconds':round(time.monotonic()-start,3)}
    (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='denominator_checks'},indent=2))
    # Article table snippets, generated solely from the computed values.
    with (out/'diagonal_table.tex').open('w') as f:
        for r in rows:
            f.write(str(r['m'])+' & '+ ' & '.join(r[f'relative_error_order_{j}'] for j in range(4))+' \\\\\n')
    print(f'Wrote reproducible results to {out}')

if __name__=='__main__':
    if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m',type=int,default=200)
    args=parser.parse_args()
    run(args.max_m)
