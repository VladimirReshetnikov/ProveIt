#!/usr/bin/env python3
"""Exact finite checks for the adaptive nine-group asymptotic certificate.

Only Python's standard library is used. Rational interval arithmetic certifies
the displayed coefficients; integer power comparisons inspect finite schedules.
Finite schedule samples supplement, and do not replace, the asymptotic proof.
"""

from fractions import Fraction as Q
from math import isqrt
import argparse
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def atan_inverse_interval(q, terms=64):
    x = Q(1, q)
    value = sum(((-1) ** j * x ** (2 * j + 1) / (2 * j + 1)
                 for j in range(terms)), Q(0))
    next_term = (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(value, value + next_term), max(value, value + next_term)


def log_ratio_interval(x, terms=96):
    """Interval for ln((1+x)/(1-x)), 0<x<1, by a positive series."""
    check(0 < x < 1, "invalid logarithm series argument")
    value = 2 * sum((x ** (2*j+1) / (2*j+1) for j in range(terms)), Q(0))
    tail = 2*x**(2*terms+1)/((2*terms+1)*(1-x*x))
    return value, value+tail


def sqrt_decimal_interval(lo, hi, digits=12):
    """Rational lower/upper square-root endpoints printed as decimal strings."""
    scale=10**digits
    low=isqrt(lo.numerator*scale*scale//lo.denominator)
    high=isqrt(hi.numerator*scale*scale//hi.denominator)+1
    def fmt(n):
        return str(n//scale)+"."+str(n%scale).zfill(digits)
    check(Q(low,scale)**2<=lo, "invalid square-root lower interval")
    check(Q(high,scale)**2>=hi, "invalid square-root upper interval")
    return [fmt(low),fmt(high)]


def exact_constants():
    # Machin's identity pi=16 atan(1/5)-4 atan(1/239).
    a0,a1=atan_inverse_interval(5)
    b0,b1=atan_inverse_interval(239)
    pi0,pi1=16*a0-4*b1,16*a1-4*b0
    l20,l21=log_ratio_interval(Q(1,3))
    l30,l31=log_ratio_interval(Q(1,2))
    l90,l91=2*l30,2*l31
    common0=pi0*pi0*l90/(l21**3)
    common1=pi1*pi1*l91/(l20**3)
    time0,time1=Q(7328,405)*common0,Q(7328,405)*common1
    space0,space1=Q(160,9)*common0,Q(160,9)*common1
    oldt0=Q(24339,400)*pi0*pi0/(l21*l21)
    olds0=Q(915,16)*pi0*pi0/(l21*l21)
    check(time1<Q(3433,100)**2, "time coefficient not below 34.33")
    check(time0>Q(3432,100)**2, "time coefficient not above 34.32")
    check(space1<Q(3403,100)**2, "space coefficient not below 34.03")
    check(space0>Q(3402,100)**2, "space coefficient not above 34.02")
    check(time1<oldt0, "new time bound fails to beat cached-tree predecessor")
    check(space1<olds0, "new space bound fails to beat cached-tree predecessor")
    check(Q(57,175)<Q(916,2025), "triangle is not below triple construction")
    check(Q(708,2025)<Q(916,2025), "pair construction is not subordinate")
    # (4/(9-2sqrt(2)))^2 < 916/2025 iff 49124 > 32976 sqrt(2).
    check(49124**2>2*32976**2, "cached recursion does not close")
    # log_2(9)<317/100, and therefore fresh-side exponent is <.232.
    check(9**100<2**317, "logarithm comparison failed")
    # log_2(9)>25/8 implies 1/(10 log_2(9))<.032.
    check(9**8>2**25, "lower logarithm comparison failed")
    return {
        "time_coefficient_interval":sqrt_decimal_interval(time0,time1),
        "space_coefficient_interval":sqrt_decimal_interval(space0,space1),
        "safe_eventual_time_coefficient":"34.33",
        "safe_eventual_space_coefficient":"34.03",
        "adaptive_triangle_squared":"57/175",
        "largest_merge_squared":"916/2025",
        "cache_squared":"16/81",
        "storage_squared":"4/9",
        "strict_predecessor_improvement":True,
        "root_dominates_full_recurrence":True,
        "arithmetic":"exact rational intervals and integer comparisons",
    }


def ceil_log2(n):
    check(n>=1,"nonpositive logarithm argument")
    return (n-1).bit_length()


def ceil_sqrt(n):
    q=isqrt(n)
    return q+(q*q<n)


def capacity_j(lam):
    # Search exact inequality 9^(20j)<=2^lambda.
    lo,hi=0,lam//60+1
    target=1<<lam
    while lo+1<hi:
        m=(lo+hi)//2
        if 9**(20*m)<=target:
            lo=m
        else:
            hi=m
    check(9**(20*lo)<=target<9**(20*(lo+1)), "capacity search failed")
    return lo


def inspect_schedule(lam):
    check(lam%10==0,"sample lambda must be divisible by 10")
    U=capacity_j(lam)-ceil_sqrt(lam)
    check(U>0,"sample too small for active schedule")
    # b=ceil(6 log_2(lambda)), computed exactly from lambda^6.
    b=ceil_log2(lam**6)
    # This is at least ceil(log_4 lambda)+2 and remains a valid bootstrap range.
    dmax=(ceil_log2(lam)+1)//2+2
    a=0
    olda=0
    rows=[]
    # An extra sqrt(lambda) bits of domination witnesses a strict finite gap.
    margin=isqrt(lam)
    # lambda^5 covers polylog overhead plus s/M<=lambda.
    overhead=lam**5
    for d in range(dmax+1):
        u=U//(1<<d)
        check(u>0,"taper vanished within the bootstrap depth range")
        a+=u+b
        q=9**a
        if d==0:
            check(q*q*overhead<=(1<<(lam//10-margin)),
                  "root symmetric gate lacks the stated strict margin")
        else:
            check(q*overhead<=(1<<(lam//10-margin)),
                  "retained-side asymmetric gate lacks the stated strict margin")
            check(q*q*(1<<(olda+1))*overhead<=(1<<(lam-margin)),
                  "fresh-side asymmetric gate lacks the stated strict margin")
        check(q*q*(1<<a)*overhead<=(1<<(lam-margin)),
              "packet rounding gate lacks the stated strict margin")
        check(a+1<9*lam//10,"new packet degree violates root cap")
        rows.append({"depth":d,"u":u,"a":a})
        olda=a
    return {"lambda":lam,"U":U,"buffer":b,"depths_checked":len(rows),
            "minimum_u":rows[-1]["u"],"maximum_a":rows[-1]["a"],
            "certified_extra_gap_bits":margin,"all_integer_gates":True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--constants-only",action="store_true")
    args=parser.parse_args()
    result={"constants":exact_constants(),
            "scope":"finite checks support the accompanying asymptotic proof"}
    if not args.constants_only:
        result["schedule_samples"]=[inspect_schedule(n) for n in
                                     (1_000_000,2_000_000,4_000_000)]
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
