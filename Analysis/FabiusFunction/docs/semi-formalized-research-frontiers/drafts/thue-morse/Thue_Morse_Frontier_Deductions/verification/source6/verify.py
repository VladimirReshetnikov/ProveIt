#!/usr/bin/env python3
"""Reproducible checks for 'Three New Directions in Thue--Morse Calculus'.

Python 3.10+; dependencies: mpmath, sympy. Optional plots require matplotlib.
Run: python verify.py [--plots]
All combinatorial checks use integers or fractions. Numerical computations are
independent checks, NOT substitutes for the proofs in the accompanying paper.
The positive series is used near q=1 to avoid catastrophic cancellation.
"""
from __future__ import annotations
import argparse, csv, itertools, json, math, random
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent

def eps(n: int) -> int:
    if n < 0:
        raise ValueError('The index must be nonnegative.')
    return -1 if n.bit_count() & 1 else 1

def corr(shifts: tuple[int, ...], m: int, cyclic: bool=False) -> int:
    if not shifts or min(shifts) < 0 or m < 0:
        raise ValueError('Nonempty nonnegative shifts and level required.')
    N = 1 << m
    return sum(math.prod(eps((n+h) % N if cyclic else n+h)
                         for h in shifts) for n in range(N))

def defect(shifts: tuple[int, ...]) -> int:
    if not shifts or min(shifts) != 0:
        raise ValueError('Nonempty shifts with minimum zero are required.')
    H = max(shifts)
    total = 0
    for t in range(1, H+1):
        if sum(h >= t for h in shifts) % 2:
            total += math.prod(eps(t-h-1) if h < t else eps(h-t)
                               for h in shifts)
    return total

def eta_finite(shifts: tuple[int, ...]) -> Fraction:
    """One-block boundary formula; no limit or recursive correlations used."""
    if len(shifts) % 2:
        return Fraction(0)
    m = max(shifts).bit_length()
    N = 1 << m
    return (Fraction(corr(shifts, m)) +
            Fraction(2, 3) * (-1)**m * defect(shifts)) / N

def cover_series(m: int, terms: dict[int, int], order: int) -> list[Fraction]:
    """Coefficients of the signed EGF from the covering-family formula.

A hyperedge is a nonempty bit mask. A polynomial x(b) is the sum of
terms[mask] * product(b_i for i in mask); the constant term is zero here.
"""
    full = (1 << m)-1
    edges = list(terms)
    answer = [Fraction(0) for _ in range(order+1)]
    for choose in range(1 << len(edges)):
        union = 0
        selected = []
        for i, edge in enumerate(edges):
            if (choose >> i) & 1:
                union |= edge
                selected.append(edge)
        if union != full:
            continue
        poly = [Fraction(1)] + [Fraction(0)]*order
        for edge in selected:
            c = terms[edge]
            nxt = [Fraction(0)]*(order+1)
            for i, p in enumerate(poly):
                for j in range(1, order-i+1):
                    nxt[i+j] += p*Fraction(c**j, math.factorial(j))
            poly = nxt
        for j in range(order+1):
            answer[j] += (-1)**m * poly[j]
    return answer

def direct_moments(m: int, terms: dict[int, int], order: int) -> list[int]:
    result = [0]*(order+1)
    for b in range(1 << m):
        x = sum(c for edge, c in terms.items() if (b & edge) == edge)
        for r in range(order+1):
            result[r] += eps(b) * x**r
    return result

def matching_polynomial(m: int, a: list[int], edges: dict[tuple[int,int],int]):
    """Coefficient list for sum_M theta^|M| J_M product a_unmatched."""
    theta = sp.Symbol('theta')
    def visit(vertices: tuple[int, ...]):
        if not vertices:
            return sp.Integer(1)
        i, *rest = vertices
        ans = a[i]*visit(tuple(rest))
        for j in rest:
            key = (min(i,j), max(i,j))
            if key in edges:
                ans += theta*edges[key]*visit(tuple(k for k in rest if k != j))
        return ans
    return sp.expand(visit(tuple(range(m))))

def logA(x):
    """log prod_{j>=0}(1-exp(-2^j x)), for x>0, at current precision."""
    x = mp.mpf(x)
    if x <= 0:
        raise ValueError('x must be positive.')
    y, total = x, mp.mpf('0')
    cutoff = (mp.mp.dps+20)*mp.log(10)
    while y < cutoff:
        total += mp.log(-mp.expm1(-y))
        y *= 2
    return total

def logQ_small(x):
    """Convergent Bernoulli series for Q(x); used with 0<x<=1."""
    x = mp.mpf(x)
    if not (0 < x <= 1.01):
        raise ValueError('This implementation requires 0<x<=1.01.')
    total = -x/2
    for r in range(1, 10000):
        term = (mp.bernoulli(2*r)*x**(2*r) /
                (2*r*mp.factorial(2*r)*(mp.mpf(2)**(2*r)-1)))
        total += term
        if abs(term) < mp.eps * max(1,abs(total)):
            return total
    raise RuntimeError('Bernoulli series failed to converge.')

def psi(v):
    """Positive smooth one-periodic amplitude, evaluated on one period."""
    v = mp.mpf(v)
    v -= mp.floor(v)
    a = mp.log(2)
    x = mp.exp(-a*v)
    return mp.exp(logA(x) + logQ_small(x) + a*(v*v+v)/2)

def flat_sum(t, z):
    """Positive F=-log Phi. Returns (value, rigorous r-tail bound, cutoff).

The only non-rigorous component in this function is floating-point evaluation
of A. The stated tail bound concerns omission of r>R, using 0<A<=1.
"""
    t, z = mp.mpf(t), mp.mpf(z)
    if t <= 0 or not 0 < z < 1:
        raise ValueError('Require t>0 and 0<z<1.')
    beta = -mp.log(z)
    w = mp.lambertw(mp.log(2)*beta/(mp.sqrt(2)*t))
    rstar = w/(mp.log(2)*beta)
    base = -beta*rstar + logA(t*rstar) - mp.log(rstar)
    # An absolute geometric tail safely below an estimated relative target.
    target_log = base - (mp.mp.dps-15)*mp.log(10)
    R = max(20, int(mp.ceil(-target_log/beta))+20)
    s = mp.fsum(mp.exp(-beta*r + logA(t*r))/r for r in range(1,R+1))
    tail = z**(R+1)/((R+1)*(1-z))
    return s, tail, R

def saddle(t, z, correction: bool=False):
    t, z = mp.mpf(t), mp.mpf(z)
    a, beta = mp.log(2), -mp.log(z)
    w = mp.lambertw(a*beta/(mp.sqrt(2)*t))
    theta = w/a + mp.mpf('0.5')
    pref = (t*mp.exp(a/8)/beta * mp.sqrt(2*mp.pi*w/a) *
            mp.exp(-(w*w+2*w)/(2*a)))
    value = psi(theta)
    if correction:
        p1 = mp.diff(psi,theta,1)
        p2 = mp.diff(psi,theta,2)
        value += ((a/12-mp.mpf('0.5'))*value-p1/2+p2/(2*a))/w
    return pref*value, w

def gaussian_coefficients(order: int):
    """Universal Laplace coefficient c_order in A(1), A'(1), ... ."""
    symbols = sp.symbols('A0:'+str(2*order+1))
    total = sp.Integer(0)
    def rec(j, remaining, ks):
        nonlocal total
        if j > 2*order+2:
            ell = remaining
            if ell < 0 or ell > 2*order:
                return
            degree = ell + sum(d*k for d,k in ks.items())
            coefficient = symbols[ell]/sp.factorial(ell)
            for d,k in ks.items():
                coefficient *= sp.Rational((-1)**(d+1),d)**k / sp.factorial(k)
            total += coefficient*sp.factorial2(degree-1)
            return
        for k in range(remaining//(j-2)+1):
            rec(j+1,remaining-(j-2)*k,{**ks,j:k})
    rec(3,2*order,{})
    return sp.expand(total)

def alternating_bits(n: int) -> int:
    """Sum (-1)^j b_j over the binary digits of a nonnegative integer."""
    if n < 0:
        raise ValueError('Nonnegative index required.')
    return sum((-1)**j*((n >> j)&1) for j in range(n.bit_length()))

def check_extended_correlations():
    """Independent integer checks of odd-order and block-multiple formulas."""
    rng = random.Random(410926)
    count = 0
    for p in range(1,9):
        for _ in range(10):
            hs = tuple(sorted([0]+[rng.randrange(18) for _ in range(p-1)]))
            m = max(1,max(hs).bit_length()); N=1 << m
            d = defect(hs)
            if p % 2:
                for level in range(m,m+4):
                    assert corr(hs,level) == -2*d
                    assert corr(hs,level,True) == 0
                    count += 2
            for Q in (0,1,2,3,5,7,10,13):
                direct = sum(math.prod(eps(n+h) for h in hs) for n in range(Q*N))
                if p % 2:
                    expected = d*(eps(Q)-1)
                else:
                    expected = Q*N*eta_finite(hs)-Fraction(2,3)*(-1)**m*d*alternating_bits(Q)
                assert direct == expected
                count += 1
    return count

def boundary_layer_examples():
    """Direct logarithmic-product data for the diagonal boundary layer.

    The absolute j-tail is bounded as in the paper. These values check
    convergence numerically, not the all-orders error theorem itself.
    """
    rows=[]
    for t in map(mp.mpf,('1','.5','.25','.125','.0625')):
        z=q=mp.exp(-t)
        J=int(mp.ceil((mp.mp.dps+15)*mp.log(10)/t))
        logphi=mp.fsum(eps(j)*mp.log1p(-z*q**j) for j in range(J))
        value=mp.exp(logphi)
        rows.append([str(t),mp.nstr(value,22),
                     mp.nstr(value-1/mp.sqrt(2),10),
                     mp.nstr(abs(logphi+mp.log(2)/2),10)])
    with (HERE/'boundary_layer.csv').open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['t','Phi_q_q','error_from_1_sqrt2','log_error'])
        writer.writerows(rows)
    return rows

def run_checks(make_plots=False):
    mp.mp.dps = 80
    rng = random.Random(20260904)
    cases = []
    for length in (2,4,6,8):
        for _ in range(30):
            cases.append(tuple(sorted([0]+[rng.randrange(0,22) for _ in range(length-1)])))
    exact_corr_checks = 0
    for h in cases:
        d, eta = defect(h), eta_finite(h)
        for m in range(max(h).bit_length(), max(h).bit_length()+5):
            N = 1 << m
            assert Fraction(corr(h,m)) == N*eta-Fraction(2,3)*(-1)**m*d
            assert Fraction(corr(h,m,True)) == N*eta+Fraction(4,3)*(-1)**m*d
            assert Fraction(corr(h,m)+corr(h,m+1),3*N) == eta
            exact_corr_checks += 3
    correlation_rows = []
    for h in ((0,1),(0,2),(0,3),(0,1,2,3),(0,1,3,7),(0,2,5,9),(0,1,2,4,7,11)):
        m = max(h).bit_length()
        correlation_rows.append([str(h),m,defect(h),str(eta_finite(h)),corr(h,m),corr(h,m,True)])
    with (HERE/'correlations.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['shifts','m','defect','eta','noncyclic_sum','cyclic_sum']);writer.writerows(correlation_rows)
    hyper_checks = 0
    for m in range(2,7):
        terms={1 << i:i+1 for i in range(m)}
        for i in range(m-1):
            terms[(1 << i)|(1 << (i+1))]=2
        # Keep enumeration manageable while still including overlapping edges.
        order=m+2
        direct=direct_moments(m,terms,order)
        predicted=cover_series(m,terms,order)
        assert all(predicted[r]*math.factorial(r)==direct[r] for r in range(order+1))
        hyper_checks+=order+1
    path_rows=[]
    for m in range(2,11):
        terms={1<<i:2**i for i in range(m)}
        for i in range(m-1):terms[(1<<i)|(1<<(i+1))]=1
        r=(m+1)//2
        moments=direct_moments(m,terms,r)
        expected=(math.factorial(r) if m%2==0 else
                  -math.factorial(r)*(sum(4**j for j in range(r))+(r-1)))
        assert all(x==0 for x in moments[:r])
        assert moments[r]==expected
        path_rows.append([m,r,expected])
    # Crossover: direct coefficient of exp(t L + theta t^2 Q).
    theta=sp.Symbol('theta')
    cross_checks=0
    for m in range(2,8):
        aa=list(range(1,m+1));edges={(i,i+1):1 for i in range(m-1)}
        direct=sp.Integer(0)
        for mask in range(1<<m):
            lin=sum(aa[i] for i in range(m) if (mask>>i)&1)
            quad=sum(w for (i,j),w in edges.items() if ((mask>>i)&1) and ((mask>>j)&1))
            direct+=eps(mask)*sum(sp.Rational(lin**(m-2*k)*quad**k,
                math.factorial(m-2*k)*math.factorial(k))*theta**k for k in range(m//2+1))
        assert sp.expand(direct-(-1)**m*matching_polynomial(m,aa,edges))==0
        cross_checks+=1
    numerical=[]
    for L in (10,20,40,80):
        t=mp.exp(-L); z=mp.mpf('0.5')
        F,tail,R=flat_sum(t,z)
        lead,w=saddle(t,z)
        corrected,_=saddle(t,z,True)
        numerical.append([L,mp.nstr(w,14),mp.nstr(mp.log10(F),16),
              mp.nstr(lead/F-1,12),mp.nstr(corrected/F-1,12),mp.nstr(tail/F,5),R])
    with (HERE/'saddle.csv').open('w',newline='') as f:
        wri=csv.writer(f);wri.writerow(['log_1_t','w','log10_F','leading_relative_error','corrected_relative_error','series_tail_relative_bound','cutoff']);wri.writerows(numerical)
    with (HERE/'path_moments.csv').open('w',newline='') as f:
        wri=csv.writer(f);wri.writerow(['number_of_bits','first_nonzero_degree','first_nonzero_moment']);wri.writerows(path_rows)
    # Independent product-versus-positive-series checks at non-extreme q.
    product_checks=[]
    for t,z in ((mp.mpf('.4'),mp.mpf('.3')),(mp.mpf('.1'),mp.mpf('.5'))):
        q=mp.exp(-t)
        J=int(mp.ceil((mp.mp.dps+10)*mp.log(10)/t))
        direct=mp.fsum(eps(j)*mp.log1p(-z*q**j) for j in range(J))
        F,tail,R=flat_sum(t,z)
        residual=abs(direct+F)
        assert residual < mp.mpf('1e-65')
        product_checks.append(mp.nstr(residual,5))
    periodic_error=abs(psi(mp.mpf('.314'))-psi(mp.mpf('1.314')))
    assert periodic_error<mp.mpf('1e-70')
    # Verify the exact A--Q factorization at arbitrary log phases.
    factorization_errors=[]
    a=mp.log(2)
    for x in (mp.mpf('.7'),mp.mpf('.01'),mp.mpf('1e-15')):
        L=mp.log(1/x)
        pred=-L*L/(2*a)-L/2+mp.log(psi(L/a))-logQ_small(x)
        error=abs(pred-logA(x));factorization_errors.append(mp.nstr(error,5))
        assert error<mp.mpf('1e-65')
    summary={'seed':20260904,'decimal_precision':mp.mp.dps,
        'exact_correlation_assertions':exact_corr_checks,
        'additional_odd_and_block_correlation_assertions':check_extended_correlations(),
        'hypergraph_moment_equalities':hyper_checks,'path_examples':len(path_rows),
        'matching_crossover_checks':cross_checks,
        'product_series_residuals':product_checks,
        'A_Q_factorization_residuals':factorization_errors,
        'universal_c1':str(gaussian_coefficients(1)),
        'universal_c2':str(gaussian_coefficients(2)),
        'correlation_examples':correlation_rows,'saddle_examples':numerical,
        'boundary_layer_examples':boundary_layer_examples(),
        'status':'All exact assertions passed. Numerical values are floating-point checks.'}
    (HERE/'verification_results.json').write_text(json.dumps(summary,indent=2))
    if make_plots:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        fig, ax=plt.subplots(figsize=(6.5,4.1))
        ws=[float(row[1]) for row in numerical]
        ax.loglog(ws,[abs(float(row[3])) for row in numerical],'o-',label='Leading approximation')
        ax.loglog(ws,[abs(float(row[4])) for row in numerical],'s-',label='With first correction')
        ax.set_xlabel('Lambert parameter w');ax.set_ylabel('Absolute relative error')
        ax.legend();ax.grid(True,which='both',alpha=.3);fig.tight_layout()
        fig.savefig(HERE/'saddle_errors.pdf');fig.savefig(HERE/'saddle_errors.png',dpi=180);plt.close(fig)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plots',action='store_true',help='also generate the PDF/PNG error plot')
    run_checks(parser.parse_args().plots)
