#!/usr/bin/env python3
"""Reproduce exact certificates for the A205497 spectral-recurrence article.

No network access is used. Exact checks use Python integers and SymPy rationals.
Floating-point spectral/asymptotic checks are separately labelled diagnostics.
Run: python verify.py --out-dir data
"""
from __future__ import annotations
import argparse
from itertools import permutations, product
from math import comb, gcd, factorial
from pathlib import Path
import json
import platform
import sympy as sp
import mpmath as mp

X = sp.Symbol('x')

def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)

def normalized(p: sp.Poly) -> sp.Poly:
    return sp.Poly(p.as_expr()/p.nth(0), X, domain=sp.QQ)

def denominator_polynomials(max_m: int) -> list[sp.Poly]:
    d = [sp.Poly(1, X, domain=sp.QQ), sp.Poly(1-X, X, domain=sp.QQ)]
    for m in range(2, max_m+1):
        d.append(sp.Poly(d[m-2].as_expr()-X*d[m-1].as_expr().subs(X,-X), X,
                         domain=sp.QQ))
    return d[:max_m+1]

def omega_table(max_n: int, max_m: int) -> list[list[int]]:
    """omega[m][n]: weak alternating words. H_m action uses suffix sums."""
    table = [[0]*(max_n+1) for _ in range(max_m+1)]
    for m in range(1,max_m+1):
        table[m][0] = 1
        v = [1]*m
        for n in range(1,max_n+1):
            table[m][n] = sum(v)
            suffix = [0]*(m+1)
            for j in range(m-1,-1,-1):
                suffix[j] = suffix[j+1]+v[j]
            v = [suffix[m-1-i] for i in range(m)]
    return table

def z_value(omega: list[list[int]], n: int, k: int) -> int:
    if k < 0:
        return 0
    return sum((-1)**j * comb(n+1,j)*omega[k+1-j][n]
               for j in range(min(k,n+1)+1))

def big_return_row(n: int) -> list[int]:
    row = [0]*max(1,n-1)
    for p in permutations(range(n)):
        if not all((p[i]<p[i+1]) if i%2==0 else (p[i]>p[i+1])
                   for i in range(n-1)):
            continue
        pos = [0]*n
        for i,v in enumerate(p): pos[v]=i
        k = sum(pos[i]>pos[i+1]+1 for i in range(n-1))
        row[k] += 1
    return row

def int_coeffs(p: sp.Poly) -> list[int]:
    result=[]
    for i in range(p.degree()+1):
        c=p.nth(i)
        require(c.q==1,'Nonintegral certificate coefficient')
        result.append(int(c))
    return result

def exact_column(k: int, d: list[sp.Poly]) -> tuple[sp.Poly,sp.Poly]:
    """Build C_k=N/R exactly, with a polynomial derivative numerator algorithm."""
    if k==0: return sp.Poly(1,X,domain=sp.QQ),d[1]
    M=k+1
    R=sp.Poly(1,X,domain=sp.QQ)
    for m in range(1,M+1): R=normalized(sp.lcm(R,d[m]**(M+1-m)))
    B=sp.Poly(0,X,domain=sp.QQ)
    for m in range(1,M+1):
        j=M-m
        E=sp.Poly(d[m-1].as_expr().subs(X,-X),X,domain=sp.QQ)
        if j==0:
            term=E
        else:
            S=E.mul(sp.Poly(X,X,domain=sp.QQ))
            p=1
            for _ in range(j):
                S=S.diff()*d[m]-p*S*d[m].diff()
                p+=1
            term=S*sp.Poly(X**(j-1)/factorial(j),X,domain=sp.QQ)
        B += (-1)**j*term*R.exquo(d[m]**(j+1))
    N=B.exquo(sp.Poly(X**(k+2),X,domain=sp.QQ))
    require(sp.gcd(N,R).degree()==0,f'Nonminimal denominator for column {k}')
    require(N.degree()==R.degree()-k-3,f'Numerator degree for column {k}')
    require(N.nth(0)==1,f'Constant numerator for column {k}')
    return N,R

def totients(n: int) -> list[int]:
    phi=list(range(n+1))
    for p in range(2,n+1):
        if phi[p]==p:
            for j in range(p,n+1,p): phi[j]-=phi[j]//p
    return phi

def orders(max_k: int) -> list[int]:
    phi=totients(2*max_k+3)
    result=[]; count=0; r=0
    for M in range(1,max_k+2):
        q=2*M+1
        new=phi[q]//2
        if q%3==0 and q>=9: new+=phi[q//3]//2
        count+=new
        r+=count
        result.append(r)
    return result

def degree_formula(k: int) -> int:
    M=k+1
    return sum(int(sp.totient(q))//2*(M+1-(q-1)//2)
               for q in range(3,2*M+2,2))+sum(
        int(sp.totient(q))//2*(M+1-(3*q-1)//2)
        for q in range(3,(2*M+1)//3+1,2))

def spectral_parameters(m: int) -> tuple[mp.mpf,mp.mpf,mp.mpf]:
    t=mp.pi/(4*m+2)
    rho=1/(2*mp.sin(t))
    alpha=4*rho*mp.cos(t)**2/(2*m+1)
    delta=t*mp.cot(t)/(mp.mpf(m)+mp.mpf('0.5'))
    return rho,alpha,delta

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-column',type=int,default=12)
    ap.add_argument('--max-row',type=int,default=100)
    ap.add_argument('--gcd-bound',type=int,default=40)
    ap.add_argument('--out-dir',type=Path,default=Path(__file__).parent/'data')
    args=ap.parse_args()
    if not 0<=args.max_column<=30 or not 9<=args.max_row<=1000 or args.gcd_bound<1:
        ap.error('Use 0<=max-column<=30, 9<=max-row<=1000 and gcd-bound>=1.')
    out=args.out_dir;out.mkdir(parents=True,exist_ok=True)
    d=denominator_polynomials(max(args.max_column+1,args.gcd_bound,9))
    checks={}
    # Matrix determinant vs recurrence, independent symbolic calculations.
    for m in range(1,10):
        H=sp.Matrix([[int(i+j>=m-1) for j in range(m)] for i in range(m)])
        actual=sp.Poly((sp.eye(m)-X*H).det(),X,domain=sp.QQ)
        require(actual==d[m],f'Determinant identity m={m}')
    checks['matrix_determinants']='PASS: m=1..9'
    pairs=0
    for m in range(1,args.gcd_bound+1):
        for n in range(1,m+1):
            actual=normalized(sp.gcd(d[m],d[n]))
            if (m-n)%2: expected=sp.Poly(1,X,domain=sp.QQ)
            else:
                r=(gcd(2*m+1,2*n+1)-1)//2
                expected=sp.Poly(d[r].as_expr().subs(X,(-1)**(m-r)*X),X,
                                 domain=sp.QQ)
            require(actual==expected,f'GCD identity m={m}, n={n}')
            pairs+=1
    checks['polynomial_gcds']=f'PASS: {pairs} unordered pairs through {args.gcd_bound}'
    print(checks['polynomial_gcds'],flush=True)
    omega=omega_table(args.max_row,max(args.max_row,args.max_column+1))
    # Direct enumeration of weak alternating words is distinct from H action.
    for m in range(1,5):
        for n in range(0,7):
            actual=sum(all((w[i]<=w[i+1]) if i%2==0 else (w[i]>=w[i+1])
                           for i in range(n-1)) for w in product(range(m),repeat=n))
            require(actual==omega[m][n],f'Weak word count m={m}, n={n}')
    checks['weak_words']='PASS: 28 pairs, m=1..4 and n=0..6'
    triangle=[]
    for n in range(args.max_row+1):
        row=[z_value(omega,n,k) for k in range(max(1,n-1))]
        require(all(v>0 for v in row),f'Row positivity n={n}')
        require(row==row[::-1],f'Row symmetry n={n}')
        if n<=9: require(row==big_return_row(n),f'Permutation count n={n}')
        require(all(row[k]**2>=row[k-1]*row[k+1] for k in range(1,len(row)-1)),
                f'Finite log-concavity check n={n}')
        triangle.append(row)
    checks['permutation_counts']='PASS: direct alternating permutation enumeration n=0..9'
    checks['finite_row_log_concavity']=f'PASS: all rows n=0..{args.max_row}; finite evidence only'
    (out/'triangle.json').write_text(json.dumps(triangle,indent=2)+'\n')
    certificates={}
    for k in range(args.max_column+1):
        N,R=exact_column(k,d)
        r=R.degree()
        require(r==degree_formula(k),f'Totient degree k={k}')
        # Long exact recurrence / coefficient check using independent integer DP.
        end=2*r+25
        om=omega_table(end+k+2,k+1)
        C=[z_value(om,i+k+2,k) for i in range(end+1)]
        rc=int_coeffs(R);nc=int_coeffs(N)
        for i in range(end+1):
            v=sum(rc[j]*C[i-j] for j in range(min(i,r)+1))
            require(v==(nc[i] if i<len(nc) else 0),f'GF coefficient k={k}, i={i}')
        certificates[str(k)]={'numerator':nc,'denominator':rc,'degree':r,
                              'numerator_degree':N.degree(),'coefficients_checked':end+1}
        print(f'column {k}: reduced degree {r}, exact identity and coefficients PASS',flush=True)
    checks['rational_certificates']=f'PASS: columns k=0..{args.max_column}; exact polynomial gcd and identities'
    # Match the three nontrivial explicitly displayed OEIS numerators verbatim as data.
    expected={
      2:[1,0,-1,-1,-1,1],
      3:[1,1,-6,-15,21,35,-13,-51,3,21,5,1,-5,-1,-1],
      4:[1,4,-31,-67,348,418,-1893,-1084,4326,4295,-7680,-9172,9104,11627,
         -5483,-10773,1108,7255,315,-3085,-228,669,102,-23,-45,-16,11,2,-1]}
    for k,v in expected.items():
        if k<=args.max_column:
            got=certificates[str(k)]['numerator']
            if k==3:
                require([a-b for a,b in zip(got,v)]==[0]*14+[2],
                        'Expected x^14 sign discrepancy against A205497 Conjecture 5.4')
            else:
                require(got==v,f'OEIS numerator {k}')
    checks['displayed_oeis_numerators']=('PASS: columns 2 and 4 agree; column 3 has the '
       'documented A205497 sign error: numerator ends +x^14, not -x^14. '
       'The corrected sign is already printed by Xin--Zhong, Example 5.11.')
    (out/'rational_certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
    rs=orders(1000)
    for k in range(min(args.max_column,1000)+1): require(rs[k]==degree_formula(k),'Order algorithm')
    (out/'minimal_orders.txt').write_text('# k  r_k (candidate sequence; no OEIS identifier assigned)\n'+
                                        ''.join(f'{k} {r}\n' for k,r in enumerate(rs)))
    (out/'orders_table.tex').write_text(''.join(
      f'{k} & {comb(k+3,3)} & {rs[k]} & {comb(k+3,3)-rs[k]} & '+
      f'{rs[k]-k-3 if k else 0} \\\\\n' for k in range(16)))
    # Numerical diagnostics: explicitly NOT substitutes for proofs.
    mp.mp.dps=100
    max_spectral_error=mp.mpf(0)
    for m in range(1,13):
        om=omega_table(20,m)
        for n in range(21):
            val=mp.mpf(0)
            for r in range(1,m+1):
                a=(2*r-1)*mp.pi/(4*m+2)
                lam=(-1)**(r+1)/(2*mp.sin(a))
                c=4*lam*mp.cos(a)**2/(2*m+1)
                val+=c*lam**n
            err=abs(val-om[m][n])/max(1,om[m][n])
            max_spectral_error=max(max_spectral_error,err)
    require(max_spectral_error<mp.mpf('1e-90'),'Spectral numerical check')
    samples=[]
    for n,k in [(50,2),(100,5),(200,10),(500,20),(1000,40),(2000,80)]:
        om=omega_table(n,k+2)
        exact=z_value(om,n,k)
        rho,alpha,delta=spectral_parameters(k+1)
        error=abs(mp.mpf(exact)/(alpha*rho**n)-1)
        q=mp.exp(-n*delta)
        bound=4*mp.power(2,-n)+2*mp.expm1((n+1)*mp.log1p(q))
        require(error<=bound,'Uniform analytic bound numerical check')
        log_ratio=2*mp.log(exact)-mp.log(z_value(om,n,k-1))-mp.log(z_value(om,n,k+1))
        samples.append({'n':n,'k':k,'relative_error':mp.nstr(error,14),
                        'rigorous_formula_bound_evaluated_numerically':mp.nstr(bound,14),
                        'log_concavity_log_ratio':mp.nstr(log_ratio,14)})
    report={'status':'PASS','python':platform.python_version(),'sympy':sp.__version__,
            'mpmath':mp.__version__,'exact_checks':checks,
            'numerical_diagnostics':{'precision_decimal_digits':100,
                                    'max_spectral_relative_error':mp.nstr(max_spectral_error,10),
                                    'samples':samples},
            'limits':['Finite checks do not prove unbounded assertions.',
                      'The article supplies ordinary mathematical proofs, not Lean certificates.',
                      'No OEIS edit, repository change, or claim of exhaustive priority search was made.']}
    (out/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
