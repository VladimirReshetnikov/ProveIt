#!/usr/bin/env python3
"""Exact checks for the new analytic estimates; no external dependencies.

The infinite/asymptotic statements are proved in report.tex. Finite evaluations
test the implementations and algebraic certificates, not the full SAT theorem.
"""
import json, math, sys
from fractions import Fraction as F
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
from schedule import (Schedule, ceil_log2, ceil_nth_root, taper_slope,
                      cauchy_weight, tuple_count, displayed_constants,
                      certified_cstar_interval)

counts = {}
def check(ok, label):
    if not ok:
        raise RuntimeError("FAILED: " + label)

def valuation(q):
    if q == 0:
        return 10**9
    return ((abs(q.numerator) & -abs(q.numerator)).bit_length()-1
            - ((q.denominator & -q.denominator).bit_length()-1))

def feature(z, j, b):
    # Kernel 2/(1-z*j): put the factorial entirely on the target side.
    A = F(1)
    for h in range(b):
        A *= (z-2*h)/(1-h*z)
    target = 2*math.factorial(b)*A/(1-b*z)
    source = F((1-2*b*b)*math.comb(j,b) if b <= j else 0)
    for h in range(b+1):
        source /= 1-2*h*j
    return target, source

# The Chernoff bracket is at least 1/lambda for every real lambda>=4.
# Multiplying the excess by 4*lambda^6 yields P(lambda).
# P(x+4) has these positive coefficients, an exact infinite-domain certificate.
poly = {5:4,4:-10,3:-4,2:-1,0:-2}
shift = [sum(c*math.comb(d,k)*4**(d-k) for d,c in poly.items() if d>=k)
         for k in range(6)]
check(shift == [1262,2360,1551,476,70,4], "Chernoff positive-shift polynomial")
counts["cher noff_positive_coefficients".replace(" ","")] = shift
for lam in range(4,1001):
    eta = F(1,lam*lam)
    gap = (1+F(2,lam))*(1-eta/2)-(1+F(1,4*lam**4))*(1+2*eta)
    check(gap >= F(1,lam), "Chernoff bracket")
counts["rational_bracket_instances"] = 997

taper_cases = 0
for a in range(1,10):
    L = 1 << a
    for u in range(1,a+1):
        W = sum((L>>i)*(u-i) for i in range(u))
        check(F(W,L) == 2*u-2+F(2,2**u), "Hermite count")
        for M in [1,u,2*u+1,17,53]:
            h = taper_slope(M,a,u)
            degree = M*(2*L-1)
            check(h*W > degree and (h-1)*W <= degree, "minimal integer slope")
            for i in range(u):
                D = 1 << (a-i)
                B = sum(F(j,2**j)*h*min(j,u-i) for j in range(1,a-i+1))*D
                check(B <= 6*h*D, "Hermite recovery-loss envelope")
            taper_cases += 1
counts["taper_instances"] = taper_cases

kernel_cases = 0
valuation_cases = 0
for J in [1,2,4,8]:
    for m in range(-3,5):
        for odd in [1,3,5]:
            z = F(2*m,odd)
            for j in range(J):
                terms = [feature(z,j,b) for b in range(J)]
                check(sum((r*l for r,l in terms),F(0)) == 2/(1-z*j),
                      "finite factorial Cauchy identity")
                kernel_cases += 1
                for b,(r,l) in enumerate(terms):
                    check(valuation(l)>=0, "integral source feature")
                    check(valuation(r)>=cauchy_weight(b), "target divisibility")
                    valuation_cases += 1
counts["ordinary_rational_kernel_identities"] = kernel_cases
counts["ordinary_rational_mode_valuation_checks"] = valuation_cases
counts["extension_ring_scope"] = (
    "The extension-ring congruence is proved analytically; the finite kernel tests "
    "here use ordinary rational two-integral points.")

cap_cases=0
for bits in [2,3,4,8,16,32,64,128,256,512,1024,2048,4096]:
    for offset in [0,1]:
        s=(1<<bits)+offset
        sc=Schedule.build(s)
        check((sc.delta-1)**10 < s**9 <= sc.delta**10, "exact degree ceiling")
        if sc.cap>=0:
            check(4*54**(2*sc.cap)*sc.delta*sc.lam**6 <= s, "cap feasible")
            check(4*54**(2*(sc.cap+1))*sc.delta*sc.lam**6 > s,"cap maximal")
            check(2**(sc.cap+1)<=sc.delta,"packet degree follows from cap")
        else:
            check(4*sc.delta*sc.lam**6 > s,"absent cap")
        cap_cases+=1
counts["exact_capacity_schedule_instances"] = cap_cases
counts["capacity_test_scope"] = (
    "These moderate sizes can take the declared direct fallback. "
    "Asymptotic non-fallback behavior is established by proof, not by these tests.")

budget_cases=0
for b in [2,3,9,10]:
    for K in [1,2,3,8,9,10,100,1000,10**6]:
        partial=0
        for d in range(30):
            partial += ((b-1)*K)//b**(d+1)
            check(partial <= K,"cumulative taper budget")
            budget_cases+=1
counts["integer_taper_budget_checks"] = budget_cases
check(54**45 < 2**259,"fixed schedule strict packing slack")

lo, hi = certified_cstar_interval()
check(F(94748,1000)<lo<hi<F(94749,1000),"certified constant enclosure")
counts["certified_C_star"] = {
    "lower":str(lo), "upper":str(hi),
    "decimal_lower":f"{float(lo):.12f}", "decimal_upper":f"{float(hi):.12f}",
    "method":"exact rational Machin and atanh series with rigorous remainder bounds"
}
table=[]
for p in [32,64,96,128]:
    for c in [1,2,4]:
        geo, fac = tuple_count(p,c,False), tuple_count(p,c,True)
        check(fac<=geo,"mode count monotonicity")
        table.append({"precision":p,"colors":c,"geometric":geo,"factorial":fac})
counts["mode_count_instances"] = len(table)
out={"status":"passed","counts":counts,"constants":displayed_constants(),"mode_counts":table,
     "scope":"Analytic certificates, schedules and local identities; no full SAT execution or Lean build."}
target=ROOT/"results"/"analysis_checks.json"
target.parent.mkdir(parents=True,exist_ok=True)
target.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"status":"passed","counts":counts,"constants":out["constants"]},indent=2))
