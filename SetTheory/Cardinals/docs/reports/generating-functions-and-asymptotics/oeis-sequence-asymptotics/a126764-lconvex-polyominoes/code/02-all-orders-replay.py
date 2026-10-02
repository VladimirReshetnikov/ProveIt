#!/usr/bin/env python3
"""Offline reproducibility checks for the L-convex area asymptotics report.

All finite formal-series checks and integer coefficient generation use the
standard library. --extras additionally uses locally installed SymPy/mpmath.
No network access or subprocess invocation occurs in this script.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import platform
import sys

if sys.flags.optimize:
    raise SystemExit("Refusing optimized Python (-O/-OO): run with checks enabled.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def mul(a, b):
    n = len(a)
    c = [0] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:n-i]):
                if y:
                    c[i+j] += x*y
    return c


def shift(a, degree, scale=1):
    n = len(a)
    return [0]*min(degree, n) + [scale*x for x in a[:max(0, n-degree)]]


def factor(a, degree, sign):
    """Multiply by 1 + sign*q**degree, without aliasing the input."""
    return add(a, shift(a, degree, sign))


def divide_factor(a, degree, sign):
    """Divide by 1 + sign*q**degree in the truncated power-series ring."""
    require(degree > 0, "factor degree must be positive")
    c = a[:]
    for i in range(degree, len(c)):
        c[i] -= sign*c[i-degree]
    return c


def reciprocal(a):
    n = len(a)
    require(a[0] != 0, "series constant term must be invertible")
    c = [F(1, a[0])] + [F(0)]*(n-1)
    for i in range(1, n):
        c[i] = -sum(a[j]*c[i-j] for j in range(1, i+1))/a[0]
    return c


def exp_series(rate, degree):
    return [F(rate)**i/F(math.factorial(i)) for i in range(degree+1)]


def exact_forward(degree):
    """T_j has z-adic order j: j <= degree gives every requested term."""
    one = [F(1)] + [F(0)]*degree
    term = reciprocal(add(one, exp_series(-1, degree)))
    d = term[:]
    for j in range(degree):
        numerator = add(one, [-x for x in exp_series(-(j+1), degree)])
        ratio = mul(exp_series(-j, degree), numerator)
        ratio = mul(ratio, reciprocal(add(one, exp_series(-(2*j+3), degree))))
        term = [-x for x in mul(term, ratio)]
        d = add(d, term)
    b = mul(d, d)
    h = []
    for r in range(degree+1):
        poly = [F(0)]*(r+1)
        for m in range(r+1):
            k = r-m
            if k <= m+2:
                poly[m] += (4*b[m]*(-1)**k * F(2)**(m-k)
                    * F(math.factorial(m+2+k), math.factorial(m+2-k)*math.factorial(k)))
        h.append(poly)
    expected_d = [F(1,2),0,F(-1,8),F(1,8),F(-11,48),F(15,32),F(-6737,5760),F(6451,1920),F(-888521,80640)]
    expected_b = [F(1,4),0,F(-1,8),F(1,8),F(-41,192),F(7,16),F(-6317,5760),F(1529,480),F(-1702513,161280)]
    k = min(degree+1, len(expected_d))
    require(d[:k] == expected_d[:k], "displayed D coefficients disagree")
    require(b[:k] == expected_b[:k], "displayed D^2 coefficients disagree")
    return d, b, h


def area_g(degree):
    """Integer recurrence (1-q^n)^2 g_n = 2g_(n-1)-g_(n-2)."""
    older = [1] + [0]*degree
    previous = older[:]
    area = older[:]
    for n in range(1, degree+1):
        g = [2*x-y for x,y in zip(previous, older)]
        g = divide_factor(divide_factor(g, n, -1), n, -1)
        area = add(area, shift(g, n))
        area = add(area, shift(g, 2*n, -1))
        older, previous = previous, g
    return area


def area_original_f(degree):
    """Independent original f recurrence and original area GF denominator."""
    older = [1] + [0]*degree  # f_-1
    previous = older[:]      # f_0
    inv_product = older[:]   # (q;q)_(n-1)^(-2)
    area = older[:]
    for n in range(1, degree+1):
        term = divide_factor(mul(previous, inv_product), n, -1)
        area = add(area, shift(term, n))
        next_f = add([2*x for x in previous], [-x for x in factor(factor(older, n, -1), n, -1)])
        older, previous = previous, next_f
        inv_product = divide_factor(divide_factor(inv_product, n, -1), n, -1)
    return area


def exact_q_identities(degree):
    one = [1]+[0]*degree
    # D: rational summands, truncated by their q-adic valuations j(j-1)/2.
    term = divide_factor(one, 1, 1)
    d = term[:]
    j = 0
    while (j+1)*j//2 <= degree:
        term = shift(divide_factor(factor(term, j+1, -1), 2*j+3, 1), j, -1)
        d = add(d, term)
        j += 1
    # B: independent partial-theta expression.
    b = one[:]
    k = 0
    while k*(k+1) <= degree:
        term = divide_factor(factor(one, 2*k+1, -1), 2*k+1, 1)
        b = add(b, shift(term, k*(k+1), -1))
        k += 1
    require(b == d, "B theta series != D series")
    # P=(-q;q^2)_infty/(q;q)_infty^3; only factors <= degree matter.
    p, qinv = one[:], one[:]
    for k in range(1, degree+1):
        qinv = divide_factor(qinv, k, -1)
        for _ in range(3):
            p = divide_factor(p, k, -1)
        if k % 2:
            p = factor(p, k, 1)
    # Literal finite-product E expression from the exact decomposition.
    # Each outer summand starts at q^(j(j-1)/2); all omitted ones vanish.
    e = [0]*(degree+1)
    j = 0
    while j*(j-1)//2 <= degree:
        inner = [0]*(degree+1)
        for ell in range(j+1):
            term = one[:]
            for k in range(ell+1, j+1):
                term = factor(factor(term, k, -1), k, -1)
            for k in range(ell, j+1):
                term = divide_factor(term, 2*k+1, 1)
            inner = add(inner, shift(term, ell))
        outer = inner
        for k in range(1, j+1):
            outer = divide_factor(outer, k, -1)
        e = add(e, shift(outer, j*(j-1)//2, (-1)**j))
        j += 1
    r = add(one, mul(qinv, e))
    reconstructed = add(mul(p, mul(b,b)), r)
    a = area_original_f(degree)
    require(a == area_g(degree), "original f GF != g recurrence")
    require(a == reconstructed, "A != P B^2 + R as truncated exact q-series")
    return {"degree":degree, "B_equals_D":True, "f_GF_equals_g_recurrence":True,
            "A_equals_P_B_squared_plus_R":True, "initial_a":a[:37],
            "initial_B":b[:20], "initial_R":r[:20]}


def inverse_checks(h, order):
    import sympy as s
    x,w,k = s.symbols("x w kappa")
    hs = [sum(s.Rational(v.numerator, v.denominator)*k**i for i,v in enumerate(poly)) for poly in h[:order+1]]
    ell = s.series(s.log(sum(v*x**i for i,v in enumerate(hs))), x, 0, order+1).removeO().expand()
    p, log_coeffs = 3*w, []
    delta, lambert_coeffs = s.Integer(0), []
    for n in range(1, order+1):
        for kind in ("log", "Lambert"):
            c = s.Symbol("new_coefficient")
            trial = (p if kind == "log" else delta) + c*x**n
            u = 1+x*trial
            residual = trial - (3*w if kind == "log" else 0) - 3*s.log(u) + ell.subs(x,x/u)
            coefficient = s.series(residual,x,0,n+1).removeO().expand().coeff(x,n)
            require(s.diff(coefficient,c) == 1, "inverse new coefficient is not monic linear")
            solution = s.expand(-coefficient.subs(c,0))
            if kind == "log":
                p += solution*x**n
                log_coeffs.append(solution)
            else:
                delta += solution*x**n
                lambert_coeffs.append(solution)
    for kind, trial, leading in (("log",p,3*w),("Lambert",delta,0)):
        u = 1+x*trial
        residual = s.series(trial-leading-3*s.log(u)+ell.subs(x,x/u),x,0,order+1).removeO().expand()
        require(residual == 0, kind+" inverse substitution failed")
    expected_log = [9*w+3,-s.Rational(27,2)*w**2+18*w+s.Rational(21,2)+2*k**2,
        27*w**3-s.Rational(189,2)*w**2-9*w+s.Rational(45,2)-12*k**2*w-8*k**2-4*k**3]
    expected_lambert = [s.Integer(3),s.Rational(21,2)+2*k**2,s.Rational(45,2)-8*k**2-4*k**3]
    for n in range(min(order,3)):
        require(s.expand(log_coeffs[n]-expected_log[n]) == 0, "displayed log inverse disagrees")
        require(s.expand(lambert_coeffs[n]-expected_lambert[n]) == 0, "displayed Lambert inverse disagrees")
    return {"order":order,"ell":[str(ell.coeff(x,i)) for i in range(1,order+1)],
            "logarithmic_P":[str(v) for v in log_coeffs], "Lambert_centered":[str(v) for v in lambert_coeffs],
            "substitution_residual_through_order":"0"}


def numerical_checks(a, h, precision):
    import mpmath as mp
    mp.mp.dps = precision
    k = 13*mp.pi**2/24
    C = 13*mp.sqrt(2)/768
    def poly_value(poly):
        return sum(mp.mpf(v.numerator)/v.denominator*k**i for i,v in enumerate(poly))
    c = [poly_value(poly)/(2*mp.sqrt(k))**i for i,poly in enumerate(h)]
    rows = []
    terms = [v for v in [1,2,3,5,7,9] if v <= len(c)]
    for n in [100,200,500,1000,2000]:
        if n >= len(a):
            continue
        N = mp.mpf(n)-mp.mpf(1)/6
        base = C*N**(-mp.mpf(3)/2)*mp.exp(2*mp.sqrt(k*N))
        rows.append({"n":n,"relative_errors":[mp.nstr(base*sum(c[j]*N**(-mp.mpf(j)/2) for j in range(v))/a[n]-1,18) for v in terms]})
    # Independent analytic-function diagnostics, never used as a proof.
    points = [("0.2","0"),("0.6","0"),("0.78","0"),("0.35","0.25"),("0.65","0.15"),("-0.45","0.1")]
    identities = []
    for re, im in points:
        q = mp.mpc(re,im)
        cutoff = math.ceil((precision+30)*float(mp.log(10)/(-mp.log(abs(q)))))
        older = previous = mp.mpc(1)
        product = mp.mpc(1)
        A = mp.mpc(1)
        Q = O = mp.mpc(1)
        for n in range(1,cutoff+1):
            qn = q**n
            A += qn*previous/(product**2*(1-qn))
            older,previous = previous,2*previous-(1-qn)**2*older
            product *= 1-qn
            Q *= 1-qn
            if n % 2:
                O *= 1+qn
        # Finite products in E are independent of the computed value of A.
        term = 1/(1+q)
        D = term
        partial_s = mp.mpc(1)
        E = term*partial_s
        Qj = Oj = mp.mpc(1)
        j = 0
        while (j+1)*j//2 <= cutoff:
            term *= -q**j*(1-q**(j+1))/(1+q**(2*j+3))
            j += 1
            Qj *= 1-q**j
            Oj *= 1+q**(2*j-1)
            partial_s += q**j*Oj/Qj**2
            D += term
            E += term*partial_s
        Btheta = mp.mpc(1)
        j = 0
        while j*(j+1) <= cutoff:
            Btheta -= q**(j*(j+1))*(1-q**(2*j+1))/(1+q**(2*j+1))
            j += 1
        P = O/Q**3
        R = 1+E/Q
        scale = max(1,abs(A))
        err = abs(A-P*D**2-R)/scale
        err_bd = abs(Btheta-D)/max(1,abs(D))
        require(err < mp.mpf(10)**(-(precision-15)), "numerical A decomposition diagnostic failed")
        require(err_bd < mp.mpf(10)**(-(precision-15)), "numerical B=D diagnostic failed")
        identities.append({"q":re+("+" if not im.startswith("-") else "")+im+"i", "cutoff":cutoff,
            "A_decomposition_normalized_error":mp.nstr(err,8), "B_D_normalized_error":mp.nstr(err_bd,8)})
    return {"precision_decimal_digits":precision,"term_counts":terms,"asymptotic_errors":rows,
            "pointwise_identity_diagnostics":identities,
            "warning":"Floating-point diagnostics are not certified error bounds or a proof of coefficient asymptotics."}


def write_json(path, value):
    path.write_text(json.dumps(value,indent=2,sort_keys=True)+"\n",encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir",type=Path,required=True,help="new directory; existing destinations are refused")
    parser.add_argument("--max-n",type=int,default=2000)
    parser.add_argument("--q-degree",type=int,default=96)
    parser.add_argument("--series-order",type=int,default=12)
    parser.add_argument("--extras",action="store_true",help="run optional SymPy inverse and mpmath numerical diagnostics")
    parser.add_argument("--inverse-order",type=int,default=4)
    parser.add_argument("--precision",type=int,default=90)
    args = parser.parse_args()
    require(args.max_n >= 0 and args.q_degree >= 0 and args.series_order >= 0, "orders must be nonnegative")
    require(not args.extras or 1 <= args.inverse_order <= args.series_order, "inverse order must be in 1..series-order when --extras is enabled")
    require(not args.extras or args.precision >= 40, "precision must be at least 40 digits when --extras is enabled")
    require(not args.output_dir.exists() and not args.output_dir.is_symlink(), "output directory already exists; choose a fresh destination")
    versions = {"python":platform.python_version()}
    if args.extras:
        import sympy, mpmath
        versions.update(sympy=sympy.__version__,mpmath=mpmath.__version__)
    args.output_dir.mkdir(parents=True,exist_ok=False)
    out = args.output_dir
    print("Computing exact rational local and forward coefficients...",flush=True)
    d,b,h = exact_forward(args.series_order)
    write_json(out/"forward-series.json", {"degree":args.series_order,"D":[str(v) for v in d],"D_squared":[str(v) for v in b],
        "h_polynomials_in_kappa":[[str(v) for v in poly] for poly in h],
        "convention":"Lists are in increasing degree. c_r = h_r/(2*sqrt(kappa))^r."})
    print("Checking independent exact q-series identities...",flush=True)
    identities = exact_q_identities(args.q_degree)
    write_json(out/"exact-identities.json",identities)
    print("Generating exact integer a_n through n="+str(args.max_n)+"...",flush=True)
    a = area_g(args.max_n)
    (out/"coefficients.txt").write_text("".join(f"{n} {value}\n" for n,value in enumerate(a)),encoding="utf-8")
    fixture = Path(__file__).resolve().parent.parent/"data"/"coefficients-2000.txt"
    require(fixture.is_file(), "bundled reference coefficient data is missing")
    reference = [tuple(map(int,line.split())) for line in fixture.read_text().splitlines()]
    require(len(reference) == 2001, "reference must contain exactly 2001 entries, n=0..2000")
    require([n for n,_ in reference] == list(range(2001)), "reference indices are malformed")
    count = min(len(a),len(reference))
    require(a[:count] == [v for _,v in reference[:count]], "reference exact integer coefficients disagree")
    if args.extras:
        print("Checking inverse reversion with SymPy...",flush=True)
        write_json(out/"inverse-series.json",inverse_checks(h,args.inverse_order))
        print("Running real/nonreal pointwise and n<=2000 numerical diagnostics...",flush=True)
        write_json(out/"numerical-diagnostics.json",numerical_checks(a,h,args.precision))
    hashes = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file()}
    receipt = {"status":"PASS", "parameters":{"max_n":args.max_n,"q_degree":args.q_degree,"series_order":args.series_order,
        "extras":args.extras,"inverse_order":args.inverse_order,"precision":args.precision}, "versions":versions,
        "reference_coefficient_count_checked":count,"reference_sha256":hashlib.sha256(fixture.read_bytes()).hexdigest(),
        "checks":"exact algebra and independent recurrence/identity checks; optional noncertified numerical diagnostics",
        "output_sha256":hashes}
    write_json(out/"receipt.json",receipt)
    print("PASS: "+str(out.resolve()),flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ImportError) as error:
        raise SystemExit(str(error)) from error
