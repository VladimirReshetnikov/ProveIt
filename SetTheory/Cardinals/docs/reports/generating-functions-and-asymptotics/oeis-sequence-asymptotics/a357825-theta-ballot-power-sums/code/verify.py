#!/usr/bin/env python3
"""Reproduce the computations in Theta Asymptotics for High-Power Ballot Sums.

Python 3.10+; dependencies: mpmath, sympy, matplotlib.
Exact integer tests are distinguished from high-precision numerical checks.
Run from any directory: python code/verify.py --all
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
FIGURES = ROOT / 'figures'
U, T, X = sp.symbols('u t x')
OEIS_A = [1,1,2,9,98,4150,562692,211106945,404883552194,
          1766902576146876,40519034229909243476,
          2708397617879598970178238,658332084097982587522119612196,
          735037057881394837614680080889845116,
          2030001034486747324990010196845670569155080]
OEIS_B = [1,1,2,5,21,183,3424,155833,25962389,10152021001,
          18355563410823,94826525443572702,1720192707342762602561,
          135432808172830648285721490,25492564910167901918236137649748]

def ballot_row(n: int) -> list[int]:
    """B(n,n-2j), j=0,...,floor(n/2), computed exactly."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    return [math.comb(n,j)- (math.comb(n,j-1) if j else 0)
            for j in range(n//2+1)]

def powers(n: int, k: int) -> int:
    if k < 0:
        raise ValueError('k must be nonnegative')
    return sum(b**k for b in ballot_row(n))

def multisets(n: int) -> int:
    return sum(math.comb(b+n-1,n) for b in ballot_row(n))

def elementary(n: int) -> list[int]:
    """Coefficients of product_{j=0}^{n-1}(1+j*z)."""
    c = [1]
    for j in range(n):
        c.append(0)
        for q in range(len(c)-1,0,-1):
            c[q] += j*c[q-1]
    return c

def symbolic(order: int = 6) -> tuple[dict[int,sp.Expr],dict[int,sp.Expr],list[sp.Expr]]:
    if not 0 <= order <= 16:
        raise ValueError('choose a symbolic order from 0 through 16')
    A = {}
    for ell in range(1,(order+2)//2+2):
        a = -X**(2*ell+2)/sp.Integer((2*ell+2)*(2*ell+1))
        a += X**(2*ell)/sp.Integer(2*ell)
        for j in range(1,(ell+1)//2+1):
            p=2*j-1; k=ell-p
            a += sp.bernoulli(2*j)/sp.Integer(2*j*p) * (
                (1 if k==0 else 0)
                - 2**(p+1)*sp.binomial(p+2*k-1,2*k)*X**(2*k))
        A[ell]=sp.expand(a)
    q = sum((-1)**(j+1)*(U*T)**j/sp.Integer(j)
            for j in range(1,order+4))-U*T-U**2*T**2/2
    q += sum(a.subs(X,1+U*T)*T**(2*ell) for ell,a in A.items())
    master = sp.expand(-1+(T**-2-1)*q
                       +sum(T**(2*j)/sp.Integer(j*(j+1))
                            for j in range(1,order//2+2)))
    assert sp.simplify(master.coeff(T,0) + sp.Rational(5,6)+U**2)==0
    D={j:sp.expand(master.coeff(T,j)) for j in range(1,order+1)}
    R=[sp.Integer(1)]
    for j in range(1,order+1):
        R.append(sp.expand(sum(i*D[i]*R[j-i] for i in range(1,j+1))/j))
    return A,D,R

A_COEF,D_COEF,R_COEF=symbolic(6)
R_FUN=[sp.lambdify(U,p,'mpmath') for p in R_COEF]

def phase(n: int | mp.mpf, sigma: int | None=None) -> mp.mpf:
    if sigma is None:
        sigma=(int(n)+1)%2
    return (mp.sqrt(n+1)-sigma)/2

def theta_moment(alpha: mp.mpf, degree: int=0, tau: mp.mpf=mp.mpf(1)) -> mp.mpf:
    if tau <= 0 or degree < 0:
        raise ValueError('tau must be positive and degree nonnegative')
    a=alpha-mp.floor(alpha)
    # Tail is negligible at the working precision for tau near one.
    radius=max(16,int(mp.sqrt((mp.mp.dps+10)*mp.log(10)/(4*tau)))+3)
    return mp.fsum((2*(j-a))**degree*mp.exp(-4*tau*(j-a)**2)
                   for j in range(-radius,radius+2))

def F(alpha: mp.mpf, order: int) -> mp.mpf:
    a=alpha-mp.floor(alpha)
    radius=max(16,int(mp.sqrt((mp.mp.dps+20)*mp.log(10)/4))+4)
    return mp.fsum(mp.exp(-4*(j-a)**2)*R_FUN[order](2*(j-a))
                   for j in range(-radius,radius+2))

def log_scale(n: int | mp.mpf) -> mp.mpf:
    n=mp.mpf(n)
    return (n*n+mp.mpf(3)*n/2)*mp.log(2)-n*mp.log(n)-n*(1+mp.log(mp.pi))/2

def approximate_ratio(n: int | mp.mpf, order: int=6,
                      sigma: int | None=None) -> mp.mpf:
    if not 0 <= order < len(R_FUN):
        raise ValueError(f'available numerical orders: 0 through {len(R_FUN)-1}')
    alpha=phase(n,sigma)
    return mp.exp(-mp.mpf(5)/6)*mp.fsum(
        F(alpha,j)/(n+1)**(mp.mpf(j)/2) for j in range(order+1))

def log_power_sum(n: int,k: int) -> mp.mpf:
    terms=[k*mp.log(b) for b in ballot_row(n)]
    top=max(terms)
    return top+mp.log(mp.fsum(mp.exp(v-top) for v in terms))

def exact_ratio(n: int) -> mp.mpf:
    """Full sum, exact integer bases, high-precision logarithms."""
    return mp.exp(log_power_sum(n,n)-log_scale(n))

def local_ratio(n: int) -> mp.mpf:
    """Plotting evaluation: log-Gamma summands near the peak, not an interval certificate."""
    m=mp.mpf(n+1); eps=(n+1)%2
    center=int(mp.floor(phase(n))); norm=log_scale(n)
    out=[]
    for j in range(center-16,center+18):
        r=2*j+eps
        if not 0<r<=m: continue
        log_b=mp.log(r/m)+mp.loggamma(m+1)
        log_b-=mp.loggamma((m-r)/2+1)+mp.loggamma((m+r)/2+1)
        out.append(mp.exp(n*log_b-norm))
    return mp.fsum(out)

def exact_tests() -> dict:
    # Independent path dynamic program, reflection formula, and shifted-binomial formula.
    paths={0:1}; entries=0
    for n in range(101):
        row=ballot_row(n)
        for j,b in enumerate(row):
            h=n-2*j
            assert b==paths[h]
            assert b==(h+1)*math.comb(n+1,j)//(n+1)
            entries+=1
        nxt={}
        for h,v in paths.items():
            nxt[h+1]=nxt.get(h+1,0)+v
            if h: nxt[h-1]=nxt.get(h-1,0)+v
        paths=nxt
    assert [powers(n,n) for n in range(15)]==OEIS_A
    assert [multisets(n) for n in range(15)]==OEIS_B
    for n in range(1,26):
        assert math.factorial(n)*multisets(n)==sum(
            c*powers(n,n-q) for q,c in enumerate(elementary(n)))
    for s in range(2,21):
        n=s*s-2; m=n+1
        row=ballot_row(n)
        j_minus=(m-(s-1))//2; j_plus=(m-(s+1))//2
        assert row[j_minus]==row[j_plus]==max(row)
    for n in range(3,101):
        m=n+1
        for r in range(1 if m%2 else 2,m-1,2):
            left=math.comb(m,(m-r)//2)*r//m
            right=math.comb(m,(m-r-2)//2)*(r+2)//m
            assert right*r*(m+r+2)==left*(r+2)*(m-r)
    for n in range(1,101):
        assert powers(n,1)==math.comb(n,n//2)
        assert powers(n,2)==math.comb(2*n,n)//(n+1)
    expected=[1,U**3/3+2*U/3,
              U**6/18-U**4/36+11*U**2/9+sp.Rational(13,60)]
    for j,p in enumerate(expected): assert sp.simplify(R_COEF[j]-p)==0
    for j,p in enumerate(R_COEF): assert sp.expand(p.subs(U,-U)-(-1)**j*p)==0
    return {'path_entries_checked':entries,'path_n_max':100,
            'OEIS_terms_checked_each':15,'rising_factorial_identity_n_max':25,
            'fixed_powers_1_and_2_n_max':100,'coefficient_order':6,'exact_square_ties_s_range':[2,20],
            'status':'All exact integer and symbolic checks passed.'}

def numerical_tables() -> dict:
    mp.mp.dps=75
    ns=[25,50,100,200,400,800,1200]
    rows=[]
    for n in ns:
        v=exact_ratio(n)
        rows.append([n,mp.nstr(v,35)]+[mp.nstr(approximate_ratio(n,j)/v-1,25)
                                       for j in [0,1,2,4,6]])
    with (DATA/'asymptotic_errors.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','a_n/scale','relerr_J0','relerr_J1','relerr_J2','relerr_J4','relerr_J6']);w.writerows(rows)
    C=mp.sqrt(mp.pi*mp.e)/(4*mp.sqrt(2))
    sectors=[]
    for n in [20,30,40,60,80,100]:
        aa=powers(n,n);bb=multisets(n)
        actual=(mp.mpf(math.factorial(n)*bb-aa)/aa)
        leading=C*n**3*mp.power(2,-n)
        sectors.append([n,mp.nstr(actual/leading,25)])
    with (DATA/'exponential_sector.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','exact_relative_correction / (C*n^3*2^-n)']);w.writerows(sectors)
    theta0=theta_moment(mp.mpf(0));thetah=theta_moment(mp.mpf('.5'))
    constants={'liminf':mp.exp(-mp.mpf(5)/6)*thetah,
               'limsup':mp.exp(-mp.mpf(5)/6)*theta0,
               'mean':mp.exp(-mp.mpf(5)/6)*mp.sqrt(mp.pi)/2,
               'turan_liminf':4*(thetah/theta0)**2,
               'turan_limsup':4*(theta0/thetah)**2,
               'first_exponential_coefficient':C}
    (DATA/'constants.json').write_text(json.dumps({k:mp.nstr(v,55) for k,v in constants.items()},indent=2))
    return {'precision_digits':75,'asymptotic_n':ns,'exponential_sector_n':[20,30,40,60,80,100],
            'note':'High-precision numerical evaluations, not interval-arithmetic certificates.'}

def inverse_approximation(L: mp.mpf,sigma: int) -> mp.mpf:
    lam=mp.log(2);c=mp.mpf(3)/2*lam-(1+mp.log(mp.pi))/2
    s=mp.sqrt(L/lam);d=(mp.log(s)-c)/(2*lam)
    beta=phase(s+d,sigma)
    d0=-mp.mpf(5)/6+mp.log(F(beta,0));d1=F(beta,1)/F(beta,0)
    return s+d+(lam*d*d+d-d0)/(2*lam*s)-d1/(2*lam*s**mp.mpf('1.5'))

def inverse_tables() -> None:
    mp.mp.dps=65;rows=[]
    for n in [100,200,400,800,1200]:
        L=log_power_sum(n,n);sig=(n+1)%2
        initial=inverse_approximation(L,sig)
        model=lambda x: log_scale(x)+mp.log(approximate_ratio(x,6,sig))-L
        root=mp.findroot(model,(initial-mp.mpf('.1'),initial+mp.mpf('.1')))
        rows.append([n,mp.nstr(initial-n,25),mp.nstr(root-n,25)])
    with (DATA/'inverse_errors.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','explicit_inverse_minus_n','order_6_model_inverse_minus_n']);w.writerows(rows)

def square_transition_table() -> None:
    mp.mp.dps=65; rows=[]; kappa=mp.mpf('0.3')
    for s in [8,16,32]:
        for d in [-2,-1,0,1,2]:
            n=s*s-2+2*d; m=n+1; k=int(mp.nint(kappa*s**3))
            rplus=s+1
            base=rplus*math.comb(m,(m-rplus)//2)//m
            prob=mp.exp(k*mp.log(base)-log_power_sum(n,k))
            limit=1/(1+mp.exp(-4*kappa*d))
            rows.append([s,d,n,k,mp.nstr(prob,30),mp.nstr(limit,30)])
    with (DATA/'square_transition.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['s','d','n','k','full_sum_probability_upper_endpoint','logistic_limit']);w.writerows(rows)


def plots() -> None:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    mp.mp.dps=45
    ns=list(range(600,1201))
    values=[float(local_ratio(n)) for n in ns]
    leading=[float(approximate_ratio(n,0)) for n in ns]
    with (DATA/'plot_data.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','phase_mod_1','local_loggamma_ratio','leading_theta'])
        w.writerows([n,float(phase(n)%1),v,l] for n,v,l in zip(ns,values,leading))
    fig,ax=plt.subplots(figsize=(8.0,3.7))
    ax.plot(ns,values,'.',markersize=2.6,label='Normalized ballot-power sum')
    ax.plot(ns[::2],leading[::2],'-',linewidth=1.0,label='Theta approximation, even n')
    ax.plot(ns[1::2],leading[1::2],'--',linewidth=1.0,label='Theta approximation, odd n')
    ax.set_xlabel('n');ax.set_ylabel(r'$a_n/\mathcal{A}_n$')
    ax.legend(loc='upper center',bbox_to_anchor=(.5,1.18),ncol=3,fontsize=7.5);ax.grid(alpha=.2)
    fig.tight_layout();fig.savefig(FIGURES/'oscillation.pdf');fig.savefig(FIGURES/'oscillation.png',dpi=160);plt.close(fig)
    xx=[j/500 for j in range(501)]
    yy=[float(mp.exp(-mp.mpf(5)/6)*theta_moment(mp.mpf(x))) for x in xx]
    fig,ax=plt.subplots(figsize=(8.0,3.7))
    ax.plot(xx,yy,'-',linewidth=1.3,label=r'$e^{-5/6}\Theta(\alpha)$')
    ax.plot([float(phase(n)%1) for n in ns],values,'.',markersize=2.2,
            label=r'Numerical values, $600\leq n\leq1200$')
    ax.set_xlabel(r'Lattice phase $\alpha_n$ modulo 1');ax.set_ylabel(r'$a_n/\mathcal{A}_n$')
    ax.legend(fontsize=8);ax.grid(alpha=.2)
    fig.tight_layout();fig.savefig(FIGURES/'phase_collapse.pdf');fig.savefig(FIGURES/'phase_collapse.png',dpi=160);plt.close(fig)

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all',action='store_true',help='Run exact tests, numerical tables, inverses and plots.')
    parser.add_argument('--plots',action='store_true',help='Also make plots.')
    args=parser.parse_args();DATA.mkdir(exist_ok=True);FIGURES.mkdir(exist_ok=True)
    status=exact_tests()
    (DATA/'coefficients.json').write_text(json.dumps({'A':{str(k):str(v) for k,v in A_COEF.items()},
        'D':{str(k):str(v) for k,v in D_COEF.items()},'R':[str(v) for v in R_COEF]},indent=2))
    if args.all:
        status['numerics']=numerical_tables();inverse_tables();square_transition_table()
    if args.all or args.plots: plots()
    (DATA/'verification_status.json').write_text(json.dumps(status,indent=2))
    print(json.dumps(status,indent=2))

if __name__=='__main__':
    main()
