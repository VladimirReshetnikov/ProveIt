"""Exact schedule/precision checks and a labeled asymptotic ledger.

This does not implement the SAT algorithm. It never constructs s=2**lambda
for the high-lambda ledger. Logarithmic displays are numerical; all schedule
choices, boundary certificates, taper counts, and multiplier guards are exact.
Run: python3 verify_final_schedule.py [output.json]
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from math import log, log2, pi, sqrt
from pathlib import Path
import json
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def ceil_div(n, d):
    return -((-n)//d)


def ln_interval_from_atanh(z, terms):
    """Bounds for log((1+z)/(1-z)), 0<z<1, using exact rationals."""
    require(0 < z < 1 and terms >= 1, "Invalid logarithm-series parameters")
    z2, power, total = z*z, z, Fraction()
    for j in range(terms):
        total += 2*power/(2*j+1)
        power *= z2
    tail = 2*power/((2*terms+1)*(1-z2))
    return total, total+tail


@lru_cache(maxsize=None)
def log2_54_interval(terms=80):
    # 54 = 2^5 * 27/16, with (27/16-1)/(27/16+1)=11/43.
    l2, u2 = ln_interval_from_atanh(Fraction(1, 3), terms)
    lq, uq = ln_interval_from_atanh(Fraction(11, 43), terms)
    return 5+lq/u2, 5+uq/l2


def exact_A(lam):
    """Certify floor(lambda/(20 log2 54)) without exponential-size integers."""
    require(lam >= 0, "Negative lambda")
    terms = 40
    while True:
        lo, hi = log2_54_interval(terms)
        lower = Fraction(lam, 20)/hi
        upper = Fraction(lam, 20)/lo
        a0, a1 = lower.numerator//lower.denominator, upper.numerator//upper.denominator
        if a0 == a1:
            return a0
        terms *= 2
        require(terms <= 1280, "Logarithm interval did not certify A")


def schedule(lam):
    require(lam >= 1, "Lambda must be positive")
    nu = lam.bit_length()  # ceil(log2(lambda+1))
    A = exact_A(lam)
    B = A-2*nu**3
    return nu, A, B


def log2_fraction_display(value):
    require(value > 0, "Log display needs positive value")
    with localcontext() as ctx:
        ctx.prec = 65
        result = ((Decimal(value.numerator).ln()-Decimal(value.denominator).ln())
                  / Decimal(2).ln())
        return format(result, '.12f')


def v2integer(n):
    require(n != 0, "v2(0) requested")
    n = abs(n)
    return (n & -n).bit_length()-1


def v2fraction(x):
    return v2integer(x.numerator)-v2integer(x.denominator)


def integer_boundary_checks():
    lambdas = set(range(513))
    for j in range(1, 129):
        k = (54**(20*j)).bit_length()-1
        lambdas.update((k, k+1))
    negative_B, nonnegative_B = 0, 0
    for lam in sorted(lambdas):
        A = exact_A(lam)
        require(54**(20*A) <= 1 << lam, "A lower integer-power boundary failed")
        require(1 << lam < 54**(20*(A+1)), "A upper integer-power boundary failed")
        if lam:
            nu, _, B = schedule(lam)
            require(1 << (nu-1) < lam+1 <= 1 << nu, "Nu ceiling identity failed")
            negative_B += B < 0
            nonnegative_B += B >= 0
    return dict(exact_integer_power_boundaries=len(lambdas),
                negative_B_small_cases=negative_B,
                nonnegative_B_small_cases=nonnegative_B,
                negative_B_policy='These small schedules require the theorem\'s exhaustive fallback; no negative u is used.')


def high_lambda_ledger():
    rows, all_depth_checks = [], 0
    # lambda=2^e is manageable as an integer; s=2^lambda is never constructed.
    for e in (40, 48, 64, 96, 128, 160):
        lam = 1 << e
        nu, A, B = schedule(lam)
        require(B > 0, "High-lambda fixture has nonpositive B")
        sum_u = 0
        # Every depth in the bootstrap d+1<=nu, even beyond the active range.
        active_min_u, active_depths = None, 0
        largest_a = 0
        for d in range(nu):
            u = (8*B)//(9**(d+1))
            sum_u += u
            a = sum_u+(d+1)*nu**2
            require(sum_u <= B, "Geometric floor budget failed")
            require(a <= A-nu**3, "Cubic reserve failed to pay cumulative gap")
            require(a >= u, "Hermite retained levels exceed packet exponent")
            # With a bootstrap shrink M_child<=M/16, activity requires 16^d<lambda.
            if 16**d < lam:
                require(u >= 1, "An active modeled level has no retained node")
                active_min_u = u if active_min_u is None else min(active_min_u, u)
                active_depths += 1
            largest_a = max(largest_a, a)
            all_depth_checks += 1
        # Explicit inherited precision envelope: p<=s[1+nu(21+3A)]2^a_prev.
        # M>s/lambda, u<=lambda, D>=2^(a_prev+nu^2+1).
        inherited_ratio = Fraction(lam**2*(1+nu*(21+3*A)), 2**(nu**2+1))
        evaluation_ratio = Fraction(3*lam*(A+1), 2**(nu**2+1))
        require(inherited_ratio < 1, "Inherited-precision ratio is not suppressed")
        require(evaluation_ratio < 1, "Jet-evaluation ratio is not suppressed")
        # Exact rational conservative log2 envelopes. The high-moment ratio is
        # k*ceil(s^0.9)*Darr/M; the extra 1 pays for ceil(s^0.9)<=2*s^0.9.
        # All hold for 2^(lambda-1)<s<=2^lambda and M>s/lambda.
        high_moment_log_envelope = Fraction(2*nu-10*nu**3)+Fraction(11, 10)
        rounding_log_envelope = -Fraction(87*lam, 100)+nu+1
        packet_degree_log_envelope = Fraction(lam, 100)+1-Fraction(9*(lam-1), 10)
        packing_overhead_log_envelope = Fraction(5*nu, 2)-lam+1
        require(high_moment_log_envelope < 0, "High-moment packing envelope failed")
        require(rounding_log_envelope < 0, "Uniform rounding envelope failed")
        require(packet_degree_log_envelope < 0, "Packet degree envelope failed")
        require(packing_overhead_log_envelope < 0, "Quasipolynomial overhead envelope failed")
        rows.append(dict(
            lambda_power_of_two=e, lambda_integer=str(lam), nu=nu, A=str(A), B=str(B),
            bootstrap_depths_checked=nu, modeled_active_depths=active_depths,
            minimum_u_on_modeled_active_levels=str(active_min_u), largest_a=str(largest_a),
            remaining_reserve_A_minus_a=str(A-largest_a),
            log2_inherited_precision_ratio=log2_fraction_display(inherited_ratio),
            log2_jet_evaluation_ratio=log2_fraction_display(evaluation_ratio),
            conservative_log2_high_moment_ratio=str(high_moment_log_envelope),
            conservative_log2_rounding_ratio=str(rounding_log_envelope),
            conservative_log2_new_degree_ratio=str(packet_degree_log_envelope),
            conservative_log2_quasipolynomial_overhead_ratio=str(packing_overhead_log_envelope),
        ))
    return dict(scope='Exact integer schedule and sufficient inequalities, with numerical logarithmic displays; '
                      'not executions of a tensor or SAT solver. The modeled active range uses the eventual '
                      'bootstrap child shrink bound 1/16, not measured instance sizes.',
                total_bootstrap_depth_checks=all_depth_checks, rows=rows)


def hermite_checks():
    schedules, levels, multipliers, rational_products = 0, 0, 0, 0
    thin_schedules = 0
    for M in (1, 2, 5, 11):
        for a in range(1, 7):
            L = 1 << a
            Q = M*(2*L-1)
            for u in range(1, a+1):
                W = sum((L >> i)*(u-i) for i in range(u))
                require(Fraction(W, L) == 2*u-2+Fraction(2, 1 << u),
                        "Exact taper condition sum failed")
                h = ceil_div(Q+1, W)
                require((h-1)*W <= Q < h*W, "Minimal complete taper slope failed")
                q = [h*max(0, u-i) for i in range(a+1)]
                for i in range(u):
                    D = 1 << (a-i)
                    Bi = sum(j*(1 << (a-i-j))*(q[i]-q[i+j])
                             for j in range(1, a-i+1))
                    require(0 <= Bi <= 6*h*D, "Hermite loss envelope failed")
                    p = 3
                    pt = p+Bi+(q[i]-1)*(a+1-i)
                    for j in range(q[i]):
                        loss = Bi+j*(a+1-i)
                        require(pt-loss >= p, "Coefficient precision failed")
                        multipliers += 1
                    require(pt-(Bi+(q[i]-1)*(a+1-i)) == p,
                            "Endpoint precision equality failed")
                    levels += 1
                schedules += 1
                thin_schedules += a == u
    # Independent rational cardinal products on a=u as well as a>u.
    for M in (1, 3):
        for a in range(1, 5):
            L, alpha = 1 << a, 1 << (a+1)
            grid = list(range(-L, L))
            for u in range(1, a+1):
                W = sum((L >> i)*(u-i) for i in range(u))
                h = ceil_div(M*(2*L-1)+1, W)
                def qnode(t):
                    return 0 if t == 0 else h*max(0, u-v2integer(t))
                for i in range(u):
                    qi = h*(u-i)
                    Bi = sum(j*(1 << (a-i-j))*(qi-h*max(0, u-i-j))
                             for j in range(1, a-i+1))
                    for sign in (-1, 1):
                        t = sign*(1 << i)
                        E = Fraction(1)
                        for v in grid:
                            if v not in (0, t):
                                E *= Fraction(-v, t-v)**qnode(v)
                        require(v2fraction(E) == -Bi, "Rational Hermite normalizer disagrees")
                        for j in range(qi):
                            exact = E*Fraction(-t, alpha)**j
                            require(v2fraction(exact) == -Bi-j*(a+1-i),
                                    "Rational jet multiplier valuation disagrees")
                        rational_products += 1
    return dict(exact_taper_schedules=schedules, schedules_with_a_equal_u=thin_schedules,
                retained_level_loss_checks=levels, coefficient_precision_checks=multipliers,
                independent_rational_normalizer_products=rational_products,
                scope='Local exact Hermite completeness and recovery-multiplier checks, including a=u; '
                      'not a complete evaluation of arbitrary deformation polynomials.')


def coefficient_comparison():
    ln2 = log(2)
    prior = 2*pi*sqrt(4320)/(ln2*(1-3*sqrt(12)/128))
    naive = prior/sqrt(3)
    orbit = 2*pi*sqrt(Fraction(290, 3))/(ln2*(1-sqrt(10)/32))
    r, b, gamma = 54, 9, .9
    alpha = min((1-gamma)/(2*log2(r)), 1/(1+2*log2(r)))
    moment = 9*pi/(8*ln2)*sqrt(3/alpha)
    epsilon = (b-1)*alpha/b
    independent = 2*pi*sqrt(Fraction(2, 3))/(ln2*sqrt(epsilon)*(1-(2/r)*sqrt(b)))
    require(abs(moment-independent) < 1e-10, "Two high-moment coefficient formulas disagree")
    require(abs(prior-648.4410666487529) < 1e-9, "Prior coefficient mismatch")
    require(abs(orbit-98.89670023224618) < 1e-9, "Orbit coefficient mismatch")
    require(abs(moment-94.74820226) < 1e-7, "Final high-moment coefficient mismatch")
    rows=[]
    for gamma in (.9, .75, .5, 0.):
        alpha = min((1-gamma)/(2*log2(r)), 1/(1+2*log2(r)))
        C = 9*pi/(8*ln2)*sqrt(3/alpha)
        rows.append(dict(gamma=gamma, alpha=alpha, coefficient=C,
                         controlling_constraint='degree and load' if (1-gamma)/(2*log2(r))
                         <= 1/(1+2*log2(r)) else 'packet rounding'))
    return dict(scope='Numerical evaluation of proved upper-bound coefficient formulas; '
                      'neither runtime benchmarks nor runtime-ratio claims.',
                prior_refined_schedule=prior,
                naive_combination_with_factorial_modes=naive,
                polynomial_time_orbit_packing=orbit,
                high_moment_final_schedule=moment,
                prior_over_final_coefficient_ratio=prior/moment,
                naive_over_final_coefficient_ratio=naive/moment,
                r=r, b=b, generalized_gamma_comparison=rows)


def main():
    result = dict(status='passed',
                  scope='Independent final-schedule, parameter-comparison, and Hermite precision checks. '
                        'No full SAT solver, contraction solver, Lean proof, or runtime benchmark is executed.',
                  boundaries=integer_boundary_checks(),
                  asymptotic_ledger=high_lambda_ledger(),
                  hermite=hermite_checks(),
                  coefficients=coefficient_comparison())
    text = json.dumps(result, indent=2)+'\n'
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(text)
    print(text)


if __name__ == '__main__':
    main()
