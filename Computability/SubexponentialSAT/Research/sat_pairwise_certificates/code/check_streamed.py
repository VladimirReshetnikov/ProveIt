"""Exact certificates for the streamed-tree analysis (standard library only).

The checks supplement the low-degree and separator-tree proofs in report.tex. They do not execute
the imported full tensor contraction or prove the upstream SAT theorem.
"""
from fractions import Fraction as Q
from math import isqrt
import json


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def sqrt_interval(x, digits=18):
    den = 10 ** digits
    k = isqrt((x.numerator * den * den) // x.denominator)
    lo, hi = Q(k, den), Q(k + 1, den)
    require(lo * lo <= x <= hi * hi, "sqrt interval")
    return lo, hi


def atan_interval(x, terms=28):
    s = sum(((-1) ** j) * x ** (2 * j + 1) / (2 * j + 1)
            for j in range(terms))
    t = ((-1) ** terms) * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(s, s + t), max(s, s + t)


def pi_interval():
    a, b = atan_interval(Q(1, 5))
    c, d = atan_interval(Q(1, 239))
    return 16*a - 4*d, 16*b - 4*c


def ln2_interval(terms=28):
    x = Q(1, 3)
    s = 2 * sum(x ** (2*j+1) / (2*j+1) for j in range(terms))
    return s, s + 2*x**(2*terms+1) / ((2*terms+1)*(1-x*x))


def b2(r):
    return Q((r-1)*(4*r+10), 9*r*r)


def low_degree_coefficient_interval():
    # r = 32, 16, 8, then 4; cumulative taper caps 1/11,1/9,1/7,1/5.
    # Tail ratio q=63/100. All algebra before display is exact rational.
    terms = [11*b2(32), Q(99, 2*16**2)*b2(16),
             Q(63, 2*128**2)*b2(8)]
    lo = sum(sqrt_interval(x)[0] for x in terms)
    hi = sum(sqrt_interval(x)[1] for x in terms)
    q = Q(63, 100)
    qlo, qhi = sqrt_interval(q)
    clo, chi = sqrt_interval(1-q)
    numlo, numhi = sqrt_interval(Q(35, 2*512**2)*b2(4))
    lo += numlo / (chi * (1 - 1/(2*qhi)))
    hi += numhi / (clo * (1 - 1/(2*qlo)))
    plo, phi = pi_interval()
    llo, lhi = ln2_interval()
    slo, shi = sqrt_interval(Q(2))
    return lo*plo*slo/lhi, hi*phi*shi/llo


def check_tree_barrier(limit=128):
    # All labeled complete graphs in this family have only one distinguished
    # vertex, so the subset recurrence reduces exactly to the two part sizes.
    uniform = [Q(0)] * (limit+1)
    star = [Q(0)] * (limit+1)
    powers = []
    for n in range(2, limit+1):
        uniform[n] = min(Q(k*(n-k)) + max(uniform[k], uniform[n-k])
                         for k in range(1, n))
        star[n] = min(Q((n-k)*(2*k+1), 3) +
                      max(star[k], Q(2,3)*uniform[n-k])
                      for k in range(1, n))
        require(uniform[n] >= Q(n*n-1,3), "uniform lower bound")
        require(star[n] >= Q(2*n*n+2*n-4,9), "star auxiliary bound")
        if n & (n-1) == 0:
            exact = Q(2*n*n+3*n-5,9)
            require(star[n] == exact, "power-two sharp tree bound")
            require(2*exact == Q((n-1)*(4*n+10),9), "normalization")
            powers.append({"r":n,"optimal_unordered_path_cost":str(exact),
                           "b_r_squared":str(b2(n))})
    return powers


def check_schedule():
    caps = [Q(1,11), Q(1,9), Q(1,7), Q(1,5)]
    log_r = [5,4,3,2]
    delta = Q(1,12)
    for d, (a,j) in enumerate(zip(caps,log_r)):
        require((1+2*j)*a == 1, "rounding leading boundary")
        prev = delta if d == 0 else caps[d-1]
        require(2*j*a + prev < 1, "finite degree packing gate")
    require(Q(63,100)>Q(11,20), "tail depth bootstrap")
    require(Q(63,100)>Q(1,4), "tail exponent convergence")
    lo, hi = low_degree_coefficient_interval()
    require(hi < Q(16813,1000), "certified new coefficient <16.813")
    require(hi < Q(23666,1000), "strict improvement over prior 23.66617")
    return {"alphabet_schedule":[32,16,8,4],
            "cumulative_taper_caps":[str(x) for x in caps],
            "tail_ratio":"63/100", "maximum_initial_degree_exponent":"1/12",
            "C_lower":str(lo), "C_upper":str(hi),
            "C_decimal_interval":[float(lo),float(hi)],
            "eventual_safe_coefficient":"16.813"}


if __name__ == "__main__":
    result = {"scope":"New local combinatorial proof and rational schedule only; imported contraction interface unverified here.",
              "tree_barrier":check_tree_barrier(), "low_degree":check_schedule()}
    print(json.dumps(result, indent=2))
