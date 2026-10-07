#!/usr/bin/env python3
"""Certified finite checks and standalone recovery; no numerical libraries.

Run normally or under python -O. Checks deliberately use explicit raises,
not assert statements. All saved enclosures have rational endpoints. The default cutoff is no_log;
harmonic is available as a comparison. Only the explicitly labeled tail
cross-check computes exact H to choose additional validation precision.
"""
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
import json
import argparse
from validation import integer, domain, write_json, decimal_string, json_output
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def rational(x):
    if type(x) not in (int,F):
        raise ValueError("Rational output requires integer or Fraction")
    x = F(x)
    return decimal_string(x.numerator)+"/"+decimal_string(x.denominator)


def harmonic(n):
    integer("n", n)
    return sum((F(1, k) for k in range(1, n + 1)), F(0))


@lru_cache(None, typed=True)
def stirling_row(n):
    integer("n", n)
    row = [1]
    for k in range(1, n + 1):
        nxt = [0] * (k + 1)
        for j in range(1, k + 1):
            nxt[j] = row[j - 1] + (k - 1) * (row[j] if j < k else 0)
        row = nxt
    return tuple(row)


@lru_cache(None, typed=True)
def fubini_list(n):
    integer("n", n)
    values = [1]
    for r in range(1, n + 1):
        values.append(sum(comb(r, k) * values[r-k] for k in range(1, r+1)))
    return tuple(values)


def exact_h(d, n):
    domain(d, n)
    if n == 0:
        return 1
    row, f = stirling_row(n), fubini_list(d*n)
    numerator = sum((-1)**(n-j) * row[j] * f[d*j] for j in range(1, n+1))
    quotient, remainder = divmod(numerator, factorial(n))
    require(remainder == 0, "Exact H transform not integral")
    return quotient


def inclusion_h(d, n):
    domain(d, n)
    return sum(sum((-1)**(v-k) * comb(v, k) * comb(k**d, n)
                   for k in range(v+1)) for v in range(d*n+1))


def cutoff(d, n, method="no_log"):
    domain(d, n, 2)
    if method not in ("no_log", "harmonic"):
        raise ValueError("Unknown cutoff method")
    h = harmonic(n-1) if method == "harmonic" else F(1)
    target = 2 * d**d * n**(d-1) * h.numerator
    def good(m):
        return h.denominator * (6*m)**d >= target
    lo, hi = 0, 1
    while not good(hi):
        hi *= 2
    while hi-lo > 1:
        mid = (hi+lo)//2
        if good(mid):
            hi = mid
        else:
            lo = mid
    require(good(hi) and (hi == 1 or not good(hi-1)), "Cutoff minimality")
    return hi


@lru_cache(None, typed=True)
def constant_bounds(bits):
    integer("bits", bits, 1)
    target = F(1, 2**(bits+16))
    s, N = F(0), 0
    while True:
        s += F(2, (2*N+1) * 3**(2*N+1))
        N += 1
        rem = F(3, 4*(2*N+1)*9**N)
        if rem < target:
            log_bounds = (s, s+rem)
            break
    def atan_bounds(a):
        s, k = F(0), 0
        while True:
            s += F((-1)**k, (2*k+1)*a**(2*k+1))
            k += 1
            next_term = F((-1)**k, (2*k+1)*a**(2*k+1))
            if abs(next_term) < target:
                return min(s, s+next_term), max(s, s+next_term), k
    a, b, na = atan_bounds(5)
    c, e, nb = atan_bounds(239)
    pi_bounds = (16*a-4*e, 16*b-4*c)
    return log_bounds, pi_bounds, {"log_terms": N, "atan5_terms": na, "atan239_terms": nb}


class Context:
    """Closed intervals with integer endpoints, scaled by exactly 2**bits."""
    def __init__(self, bits):
        integer("bits", bits, 1)
        self.bits, self.scale = bits, 1 << bits

    def exact(self, x):
        if type(x) is not int:
            raise ValueError("Exact dyadic input must be an integer")
        return Interval(self, x*self.scale, x*self.scale)

    def from_bounds(self, lo, hi):
        if type(lo) not in (int,F) or type(hi) not in (int,F):
            raise ValueError("Bounds must be integers or Fractions")
        lo, hi = F(lo), F(hi)
        require(lo <= hi, "Reversed rational bounds")
        return Interval(self, (lo.numerator*self.scale)//lo.denominator,
                        -((-hi.numerator*self.scale)//hi.denominator))


class Interval:
    def __init__(self, ctx, lo, hi):
        if not isinstance(ctx, Context) or type(lo) is not int or type(hi) is not int:
            raise ValueError("Interval requires a Context and integer endpoints")
        require(lo <= hi, "Reversed interval")
        self.c, self.lo, self.hi = ctx, lo, hi

    def _compatible(self, other):
        if not isinstance(other, Interval) or self.c is not other.c:
            raise ValueError("Interval context mismatch")

    def __add__(self, other):
        self._compatible(other)
        return Interval(self.c, self.lo+other.lo, self.hi+other.hi)

    def __neg__(self):
        return Interval(self.c, -self.hi, -self.lo)

    def __sub__(self, other):
        self._compatible(other)
        return self + (-other)

    def __mul__(self, other):
        self._compatible(other)
        s = self.c.scale
        products = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(self.c, min(products)//s, -((-max(products))//s))

    def reciprocal(self):
        require(self.lo > 0, "Reciprocal requires positive interval")
        ss = self.c.scale**2
        return Interval(self.c, ss//self.hi, -((-ss)//self.lo))

    def scale_rational(self, value):
        if type(value) not in (int,F):
            raise ValueError("Scale factor must be an integer or Fraction")
        q = F(value)
        a, b = self.lo*q.numerator, self.hi*q.numerator
        a, b = min(a,b), max(a,b)
        return Interval(self.c, a//q.denominator, -((-b)//q.denominator))

    def width(self):
        return F(self.hi-self.lo, self.c.scale)

    def midpoint(self):
        return F(self.lo+self.hi, 2*self.c.scale)


def cmul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def evaluate(d, n, M, bits):
    domain(d, n, 1)
    integer("M", M, 1)
    integer("bits", bits, 1)
    c = Context(bits)
    lb, pb, terms = constant_bounds(bits)
    lam, pi = c.from_bounds(*lb), c.from_bounds(*pb)
    row = stirling_row(n)
    coefficients = {d*j+1: F((-1)**(n-j)*row[j]*factorial(d*j), 2*factorial(n))
                    for j in range(1, n+1)}
    total = c.exact(0)
    for m in range(M):
        if m == 0:
            inverse = lam.reciprocal(), c.exact(0)
        else:
            y = pi.scale_rational(2*m)
            inv_denom = (lam*lam+y*y).reciprocal()
            inverse = lam*inv_denom, (-y)*inv_denom
        power = c.exact(1), c.exact(0)
        for r in range(1, d*n+2):
            power = cmul(power, inverse)
            if r in coefficients:
                total += power[0].scale_rational(coefficients[r] * (1 if m == 0 else 2))
    return total, terms


def nearest_integer(value):
    if type(value) not in (int, F):
        raise ValueError("Rounding input must be an integer or Fraction")
    a = F(value)
    return (2*a.numerator+a.denominator)//(2*a.denominator)


def interval_record(enclosure, terms, tried):
    return {
        "bits": enclosure.c.bits, "precision_attempts": tried,
        "series_terms": terms, "enclosure_scale_bits": enclosure.c.bits,
        "enclosure_lower_numerator": decimal_string(enclosure.lo),
        "enclosure_upper_numerator": decimal_string(enclosure.hi),
        "interval_width": rational(enclosure.width()),
        "midpoint": rational(enclosure.midpoint())
    }


def tail_budget(d, n, method="no_log"):
    domain(d, n, 2)
    if method == "no_log":
        return F(13,18*n**(d-1)), F(1,4), F(35,72)
    if method == "harmonic":
        return F(13,18*n**d*harmonic(n-1)), F(1,2), F(31,72)
    raise ValueError("Unknown cutoff method")


def recover(d, n, method="no_log"):
    """Recover H from a finite pole sum without consulting exact_h.

    For n>=2, precision depends ONLY on the enclosure width. The analytic
    theorem bounds omitted poles; exact H is never computed or inspected.
    Endpoint n=0 is 1 and n=1 uses the elementary ordered-Bell recurrence.
    """
    domain(d, n)
    if method not in ("no_log", "harmonic"):
        raise ValueError("Unknown cutoff method")
    if n < 2:
        value = 1 if n == 0 else fubini_list(d)[d]
        return {"d":d, "n":n, "method":"endpoint identity",
                "nearest_integer":decimal_string(value), "cutoff_method":method,
                "uses_exact_h_for_refinement":False}
    M = cutoff(d, n, method)
    analytic_bound, width_limit, universal_budget = tail_budget(d,n,method)
    bits, tried = 64, []
    while True:
        enclosure, terms = evaluate(d, n, M, bits)
        tried.append(bits)
        if enclosure.width() <= width_limit:
            break
        bits *= 2
    budget = analytic_bound+enclosure.width()/2
    require(budget <= universal_budget < F(1,2), "Rounding budget insufficient")
    result = {"d":d, "n":n, "M":M, "retained_poles":2*M-1,
              "method":"pole-sum enclosure and analytic tail theorem",
              "cutoff_method":method, "required_interval_width":rational(width_limit),
              "uses_exact_h_for_refinement":False,
              "nearest_integer":decimal_string(nearest_integer(enclosure.midpoint())),
              "analytic_tail_bound_strict":rational(analytic_bound),
              "midpoint_error_budget_strict":rational(budget)}
    result.update(interval_record(enclosure, terms, tried))
    return result


def certify(d, n, recovery=None):
    """H-aware cross-check, NOT the standalone recovery algorithm.

    Refines until the exact transformed H certifies the observed tail
    below the theorem's bound. This additional stopping rule uses H.
    """
    domain(d, n, 2)
    if recovery is None:
        recovery = recover(d, n)
    require(recovery["d"] == d and recovery["n"] == n,
            "Recovery case mismatch")
    method = recovery["cutoff_method"]
    M, bits, tried = cutoff(d,n,method), recovery["bits"], []
    exact = exact_h(d,n)
    analytic_bound, width_limit, unused_budget = tail_budget(d,n,method)
    while True:
        enclosure, terms = evaluate(d,n,M,bits)
        tried.append(bits)
        observed_hi = max(abs(F(enclosure.lo,enclosure.c.scale)-exact),
                          abs(F(enclosure.hi,enclosure.c.scale)-exact))
        if enclosure.width() <= width_limit and observed_hi < analytic_bound:
            break
        bits *= 2
    recovered = nearest_integer(enclosure.midpoint())
    require(recovered == exact, "Cross-check recovery mismatch")
    require(recovery["nearest_integer"] == decimal_string(exact),
            "Standalone recovery disagrees with exact transform")
    observed_lo = max(F(0), F(enclosure.lo,enclosure.c.scale)-exact,
                      exact-F(enclosure.hi,enclosure.c.scale))
    result = {
        "d":d, "n":n, "M":M, "retained_poles":2*M-1,
        "method":"exact-H-aware rational tail cross-check", "cutoff_method":method,
        "uses_exact_h_for_refinement":True, "H":decimal_string(exact),
        "nearest_integer":decimal_string(recovered),
        "analytic_tail_bound_strict":rational(analytic_bound),
        "observed_tail_lower":rational(observed_lo),
        "observed_tail_upper":rational(observed_hi),
        "actual_tail_certified_below_analytic_bound":True,
        "standalone_recovery_matches_exact_transform":True
    }
    result.update(interval_record(enclosure,terms,tried))
    return result


def finite_inequality_checks():
    stirling_checks, factorial_checks, cutoffs = 0, 0, 0
    composition_checks, no_log_factorial_checks, no_log_cutoffs = 0, 0, 0
    for n in range(2,101):
        h, row = harmonic(n-1), stirling_row(n)
        for j in range(1,n+1):
            require(F(row[j]) <= factorial(n-1)*h**(j-1)/factorial(j-1),
                    "Harmonic Stirling bound")
            stirling_checks += 1
            require(F(row[j],factorial(n)) <= F(comb(n-1,j-1),factorial(j))
                    <= F(n**(j-1),factorial(j)*factorial(j-1)),
                    "Composition Stirling bound")
            composition_checks += 1
        for d in range(2,13):
            M = cutoff(d,n,"harmonic")
            q0 = F(d**d*n**(d-1)*h,(6*M)**d)
            require(q0 <= F(1,2), "Rational cutoff q bound")
            upper_kr = F(1,6*M)+F(1,6*(d-1))+F(1,36*M*(d-1))
            require(upper_kr <= F(13,36), "K/R bound")
            require(F(13,18*n**d*h)+F(1,4) <= F(31,72), "Rounding budget")
            cutoffs += 1
            M0 = cutoff(d,n,"no_log")
            q_no_log = F(d**d*n**(d-1),(6*M0)**d)
            require(q_no_log <= F(1,2), "No-log cutoff q bound")
            upper_no_log_kr = F(1,6*M0)+F(1,6*(d-1))+F(1,36*M0*(d-1))
            require(upper_no_log_kr <= F(13,36), "No-log K/R bound")
            require(F(13,18*n**(d-1))+F(1,8) <= F(35,72), "No-log rounding budget")
            require(M0 <= M, "No-log cutoff larger than harmonic cutoff")
            no_log_cutoffs += 1
            for j in range(1,n+1):
                first = F(factorial(d*j),factorial(j-1))
                middle = j*d**(d*j)*factorial(j)**(d-1)
                last = j*d**d*(d**d*n**(d-1))**(j-1)
                require(first <= middle <= last, "Factorial inequality")
                factorial_checks += 1
                first0 = F(factorial(d*j),factorial(j)*factorial(j-1))
                middle0 = j*d**(d*j)*factorial(j)**(d-2)
                last0 = j*d**d*(d**d*n**(d-2))**(j-1)
                require(first0 <= middle0 <= last0, "No-log factorial inequality")
                no_log_factorial_checks += 1
    limit = 30
    W = [[F(0) for unused in range(limit+1)] for unused in range(limit+1)]
    W[0][0] = F(1)
    composition_equalities = 0
    for j in range(1,limit+1):
        for n in range(j,limit+1):
            W[j][n] = sum((W[j-1][n-k]/k for k in range(1,n-j+2)),F(0))
            require(W[j][n]/factorial(j) == F(stirling_row(n)[j],factorial(n)),
                    "Ordered-composition Stirling identity")
            composition_equalities += 1
    return {"unsigned_stirling_checks": stirling_checks,
            "factorial_chain_checks": factorial_checks,
            "cutoff_and_constant_checks": cutoffs,
            "composition_stirling_checks":composition_checks,
            "no_log_factorial_chain_checks":no_log_factorial_checks,
            "no_log_cutoff_and_constant_checks":no_log_cutoffs,
            "ordered_composition_equalities":composition_equalities,
            "ordered_composition_range_n":[1,limit],
            "range_n": [2,100], "range_d": [2,12]}


def interval_unit_checks():
    c = Context(10)
    for a in [F(-7,3),F(-1,7),F(0),F(1,9),F(17,5)]:
        ia = c.from_bounds(a,a)
        for b in [F(-3,5),F(0),F(2,7),F(14,3)]:
            ib = c.from_bounds(b,b)
            for iv, exact in [(ia+ib,a+b),(ia-ib,a-b),(ia*ib,a*b),
                              (ia.scale_rational(b),a*b)]:
                require(F(iv.lo,c.scale)<=exact<=F(iv.hi,c.scale),
                        "Outward interval arithmetic")
        if a > 0:
            iv = ia.reciprocal()
            require(F(iv.lo,c.scale)<=1/a<=F(iv.hi,c.scale), "Outward reciprocal")


def run_suite(output):
    interval_unit_checks()
    inequalities = finite_inequality_checks()
    independent = []
    for d in range(2,7):
        for n in range(0,7):
            a, b = exact_h(d,n), inclusion_h(d,n)
            require(a==b, f"Inclusion-exclusion d={d}, n={n}")
            independent.append({"d":d,"n":n,"H":decimal_string(a)})
    cases = [(d,n) for d in range(2,7) for n in (2,3,5,10)]
    cases += [(2,25),(2,50),(2,100),(3,25),(3,50),(4,25),(5,25),(8,10),(12,10)]
    recoveries, cross_checks = [], []
    for d,n in cases:
        recovery = recover(d,n)
        recoveries.append(recovery)
        cross_checks.append(certify(d,n,recovery))
    endpoint_recoveries = [recover(d,n) for d in range(2,7) for n in (0,1)]
    output_data = {
        "method":"Exact integers, Fraction constants, outward dyadic interval arithmetic",
        "uses_binary_floating_point_for_proof":False,
        "scope":"Finite exact checks and rational enclosures; universal claims require the article's proofs",
        "inequality_checks":inequalities,
        "independent_vertex_inclusion_exclusion":independent,
        "certified_integer_recoveries":recoveries,
        "exact_transform_tail_cross_checks":cross_checks,
        "endpoint_recoveries":endpoint_recoveries,
        "harmonic_cutoff_comparison":[{"d":d,"n":n,
            "no_log_M":cutoff(d,n,"no_log"), "harmonic_M":cutoff(d,n,"harmonic")}
            for d,n in cases],
        "certificate_count":len(recoveries), "all_checks_passed":True}
    write_json(output,output_data)
    print(json.dumps({"status":"PASS", "certified_recoveries":len(recoveries),
                      "exact_H_aware_cross_checks":len(cross_checks)},sort_keys=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest="command")
    suite=sub.add_parser("suite", help="run all finite exact checks")
    suite.add_argument("--output",type=Path,default=Path(__file__).with_name("rational_checks.json"))
    recovery=sub.add_parser("recover",help="recover a single H without an exact-H oracle")
    recovery.add_argument("d",type=int)
    recovery.add_argument("n",type=int)
    recovery.add_argument("--output",type=Path)
    recovery.add_argument("--cutoff",choices=["no_log","harmonic"],default="no_log")
    args=parser.parse_args()
    if args.command == "recover":
        result=recover(args.d,args.n,args.cutoff)
        if args.output:
            write_json(args.output,result)
        print(json_output(result))
    else:
        output=args.output if args.command == "suite" else Path(__file__).with_name("rational_checks.json")
        run_suite(output)


if __name__ == "__main__":
    main()
