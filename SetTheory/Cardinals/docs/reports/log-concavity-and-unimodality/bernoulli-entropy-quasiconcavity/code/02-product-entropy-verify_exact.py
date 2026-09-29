#!/usr/bin/env python3
"""Exact, dependency-free certificates for Nine Bits, Ten Bits.

This is a finite arithmetic verifier, not a proof-assistant verification of
all real-variable theorems. Run from any working directory with Python >=3.10.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from decimal import Decimal, localcontext
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = 0

def check(condition: bool, description: str) -> None:
    global CHECKS
    if not condition:
        raise AssertionError(description)
    CHECKS += 1

def dec(x: F, places: int = 24) -> str:
    with localcontext() as context:
        context.prec = places
        return str(Decimal(x.numerator) / Decimal(x.denominator))

def polynomial(y: F, m: int, k: int) -> F:
    return m*(1+y**(2*k-m))-(2*k-m)*(y**k+y**(k-m))

def isolate(m: int, k: int, steps: int = 86) -> tuple[F,F]:
    """Bracket the unique root in (0,1); uniqueness is proved in the article."""
    lo, hi = F(0), F(1)
    for _ in range(steps):
        mid = (lo+hi)/2
        value = polynomial(mid,m,k)
        if value == 0:
            return mid, mid
        if value > 0:
            lo = mid
        else:
            hi = mid
    check(polynomial(lo,m,k)>=0 and polynomial(hi,m,k)<=0,
          f"isolating signs at {m}/{k}")
    return lo,hi

def profile_bounds(m: int, k: int, lo: F, hi: F) -> tuple[F,F]:
    lower = lo**m*(1-hi**(k-m))**2/(1+hi**k)**2
    upper = hi**m*(1-lo**(k-m))**2/(1+lo**k)**2
    f = lambda beta: m*beta/(k-m+k*beta)
    return f(lower), f(upper)

def root_interval(value: F, degree: int, bits: int = 96) -> tuple[F,F]:
    """Outward dyadic bounds for value**(1/degree), for 0<=value<=1."""
    if not 0 <= value <= 1 or degree < 1:
        raise ValueError("root_interval requires 0<=value<=1 and degree>=1")
    denominator = 1 << bits
    lo,hi=0,denominator
    target = value.numerator * denominator**degree
    multiplier = value.denominator
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**degree*multiplier <= target:
            lo=mid
        else:
            hi=mid
    lower,upper=F(lo,denominator),F(hi,denominator)
    check(lower**degree<=value<=upper**degree,"outward root enclosure")
    return lower,upper

def power_sum_interval(p: F) -> tuple[F,F]:
    l1,u1=root_interval(p**20,41)
    l2,u2=root_interval((1-p)**20,41)
    return (l1+l2)**10,(u1+u2)**10

def main() -> None:
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    result: dict[str,object]={}
    # Independent PMF enumeration versus the factorized power sum.
    for n in range(1,8):
        probabilities=[F(i+1,n+3) for i in range(n)]
        pmf=[]
        for bits in product((0,1),repeat=n):
            mass=F(1)
            for p,bit in zip(probabilities,bits):
                mass*=p if bit else 1-p
            pmf.append(mass)
        check(sum(pmf)==1,f"PMF normalization n={n}")
        for q in (2,3,4,5):
            factorized=F(1)
            for p in probabilities:
                factorized*=p**q+(1-p)**q
            check(sum(mass**q for mass in pmf)==factorized,
                  f"power factorization n={n},q={q}")
    for n in range(1,13):
        sums={sum(bit*(1<<i) for i,bit in enumerate(bits))
              for bits in product((0,1),repeat=n)}
        check(len(sums)==1<<n,f"collision-free binary weights n={n}")
    # Exact finite checks of the coefficient inequality used in the proof.
    for denominator in range(2,46):
        for numerator in range(1,denominator):
            a=F(numerator,denominator)
            for k in range(2,15):
                check(1-(2-a*a)*a**(2*k-2)>=0,"hyperbolic series coefficient")
            for u in (F(0),F(1),F(3,2),F(2),F(4)):
                check(1-u+u*u/3>=F(1,4),"quadratic lower bound")
    y=F(15,16)
    beta=y**20*(1-y**21)**2/(1+y**41)**2
    rho=20*beta/(21+41*beta)
    D=(53*15**20*16**20*(16**21-15**21)**2
       -7*(16**41+15**41)**2)
    expected=int("454541702594717822238456136645128620696351269873511903070612092425935633848945080535442406921433")
    check(D==expected and D>0,"positive 96-digit integer curvature witness")
    check(10*rho>1,"positive ten-dimensional curvature")
    check(53*y**20*(1-y**21)**2-7*(1+y**41)**2==F(D,16**82),
          "cleared-denominator witness identity")
    p=F(15**41,15**41+16**41)
    epsilon=F(1,1000)
    check(0<p-epsilon<p+epsilon<1,"strictly interior rational endpoints")
    center=power_sum_interval(p)
    plus=power_sum_interval(p+epsilon)
    minus=power_sum_interval(p-epsilon)
    lower=((plus[0]+minus[0])/2-center[1])*F(41,21)
    upper=((plus[1]+minus[1])/2-center[0])*F(41,21)
    check(F(8379718,10**14)<lower<upper<F(8379719,10**14),
          "finite rational Jensen gap enclosure")
    check(F(837,10**10)<lower,"positive simple rational lower bound")
    c=F(-961,10001023)
    check(10*rho>1+c*c,"positive curvature on a weighted-mean hyperplane")
    weights=[1+F(1<<i,10**6) for i in range(10)]
    signs=[1]*5+[-1]*5
    direction=[F(sign)-c for sign in signs]
    check(sum(w*v for w,v in zip(weights,direction))==0,"exact weighted mean preservation")
    sums={sum(w*bit for w,bit in zip(weights,bits))
          for bits in product((0,1),repeat=10)}
    check(len(sums)==1024,"near-unit weights are collision-free")
    def mixed_interval(slope_parameter: F) -> tuple[F,F]:
        factors=[]
        for velocity in (1-c,1+c):
            x=p+velocity*slope_parameter
            l1,u1=root_interval(x**20,41)
            l2,u2=root_interval((1-x)**20,41)
            factors.append((l1+l2,u1+u2))
        return ((factors[0][0]*factors[1][0])**5,
                (factors[0][1]*factors[1][1])**5)
    plus_m=mixed_interval(epsilon)
    minus_m=mixed_interval(-epsilon)
    lower_m=((plus_m[0]+minus_m[0])/2-center[1])*F(41,21)
    upper_m=((plus_m[1]+minus_m[1])/2-center[0])*F(41,21)
    check(F(8378699,10**14)<lower_m<upper_m<F(8378700,10**14),
          "finite weighted-mean Jensen certificate")
    result["weighted_mean_witness"]={"weights":"w_i=1+2^(i-1)/1000000, i=1,...,10",
        "c":str(c),"direction":"five entries 1-c, followed by five entries -1-c",
        "gap_lower_exact":str(lower_m),"gap_upper_exact":str(upper_m),
        "gap_lower_approx":dec(lower_m),"gap_upper_approx":dec(upper_m)}
    result["witness"]={"q":"20/41","p":str(p),"epsilon":str(epsilon),
        "D":str(D),"rho_approx":dec(rho),"ten_rho_minus_one":dec(10*rho-1),
        "gap_lower_exact":str(lower),"gap_upper_exact":str(upper),
        "gap_lower_approx":dec(lower),"gap_upper_approx":dec(upper),
        "certified_simple_gap_bounds":["8379718/100000000000000","8379719/100000000000000"]}
    orders=[(1,100),(1,10),(1,4),(1,3),(2,5),(20,41),(1,2),(3,5),(3,4),(9,10),(99,100)]
    rows=[]
    for m,k in orders:
        if (m,k) in ((1,2),(1,3)):
            dimension=10 if k==2 else 11
            rows.append({"q":f"1/{k}","Psi_approx":dec(F(1,dimension)), "N":dimension,
                         "method":"exact analytic exceptional-order theorem"})
            continue
        lo,hi=isolate(m,k)
        lower,upper=profile_bounds(m,k,lo,hi)
        check(0<lower<=upper<F(1,9),f"profile enclosure {m}/{k}")
        Nlo=(1/upper).numerator//(1/upper).denominator
        Nhi=(1/lower).numerator//(1/lower).denominator
        check(Nlo==Nhi,f"certified dimension {m}/{k}")
        check(Nlo*upper<1 and (Nlo+1)*lower>1,f"strict threshold signs {m}/{k}")
        rows.append({"q":f"{m}/{k}","Psi_approx":dec((lower+upper)/2),"N":Nlo,
                     "isolating_interval":[str(lo),str(hi)],"method":"exact rational interval arithmetic"})
    result["profile_table"]=rows
    result["exact_checks_passed"]=CHECKS
    out=ROOT/"results"
    out.mkdir(exist_ok=True)
    (out/"certificates.json").write_text(json.dumps(result,indent=2)+"\n")
    tex=[r"\begin{tabular}{@{}rrr@{}}",r"\toprule",r"Order $q$ & $\Psi(q)$ (approximate) & Exact $N(q)$ \\",r"\midrule"]
    for row in rows:
        tex.append(f"${row['q']}$ & {float(row['Psi_approx']):.12f} & {row['N']} \\\\")
    tex += [r"\bottomrule",r"\end{tabular}"]
    (out/"profile_table.tex").write_text("\n".join(tex)+"\n")
    print(f"PASS: {CHECKS:,} exact arithmetic checks.")
    print("Curvature certificate integer D =",D)
    print("Finite Jensen gap lies strictly between 0.00000008379718 and 0.00000008379719.")
    print("Near-unit weighted-mean Jensen gap lies between 0.00000008378699 and 0.00000008378700.")
    print("All profile-table dimensions certified by exact arithmetic, except q=1/2 and q=1/3,")
    print("whose exact values N=10 and N=11 are supplied by the article's analytic theorem.")
    print("No external dependencies; no random sampling; no floating-point decisions.")
    for row in rows:
        print(f"q={row['q']:>6}, Psi~{row['Psi_approx']}, N={row['N']}")

if __name__=="__main__":
    main()
