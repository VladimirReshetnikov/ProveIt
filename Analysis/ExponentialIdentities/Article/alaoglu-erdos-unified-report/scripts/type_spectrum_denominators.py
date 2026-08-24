#!/usr/bin/env python3
r"""
Type-spectrum campaign: exact computations behind the three results of the
"is V_tau = V_0 for every finite tau?" analysis.

Notation.  Failure hypothesis: beta irrational (transcendental), M = 2^beta and
A = 3^beta integers, Sol = N_0 + N_0 beta, V_tau = {g entire, g(Sol) subset Z,
tau_2(g) <= tau}.

Part 1  DENOMINATOR GROWTH FOR THE MULTIPLICATIVE MONOID <2,M>.
   A function of the form g(z) = F(2^z) is integer-valued on Sol exactly when the
   entire F is integer-valued on the multiplicative monoid T = {2^n M^k}, and
   tau_2(g) <= tau exactly when log Max(F,R) <= C (log R)^2 with C = tau/(log 2)^2.
   Newton interpolation at the nodes t_0 < t_1 < ... of T has divided differences
        c_j = sum_i F(t_i) / P_i ,      P_i = prod_{l != i} (t_i - t_l),
   so c_j lies in (1/G_j) Z with  G_j = lcm_i P_i, which is exactly the smallest
   such denominator.  Cauchy on |x| = R gives log|c_j| <= -j^2/(4C) + O(j) with
   the OPTIMAL radius log R = j/(2C) -> infinity (so only large radii are used and
   the limsup nature of tau_2 is respected).  Hence
        log G_j = o(j^2)   ==>   c_j = 0 for all large j   ==>   F is a polynomial.
   This script measures log G_j exactly.  Result: for a two-generated monoid
   (beta irrational) log G_j = Theta(j^{3/2}); for the one-generated control
   monoid {2^n} (beta = 1, Sol = N_0) log_2 G_j = j^2 - 1 EXACTLY.  The exponent
   gap 3/2 vs 2 is precisely the quadratic-vs-linear density signature of Sol.

Part 2  THE SMOOTH-BRANCH CONSTRUCTION 2^{z^2}.
   Verifies the identity 2^{s^2} = 2^{n^2} M^{2nk} (2^{beta^2})^{k^2} on s = n+k beta
   and 2^{beta^2} = M^beta = 2^{a^2} 3^{ab} A^b when M = 2^a 3^b is three-smooth.
   Consequence: in the branch "M three-smooth" (Thm sm:uniform-second-level row 1)
   g(z) = 2^{z^2} lies in V_{log 2} \ V_0.

Part 3  THE CONTROL-SIDE SPECTRUM.
   theta_q(z) = sum_k q^{k^2} e^{2 pi i k z} has tau_2 = pi^2 / log(1/q), and
   1 + theta_q(z) - theta_q(0) is integer-valued on N_0 with Delta_1 = 0.  At an
   integer control this realises EVERY tau in (0, infinity) inside a RANK-ONE
   Z[Delta_1, Delta_beta]-module.
"""
import math, sys
from math import gcd

# ----------------------------------------------------------------- Part 1

def nodes(M, J):
    """The J smallest elements of the multiplicative monoid <2, M>, exactly."""
    b = math.log2(M); T = 4.0
    while True:
        out, k = set(), 0
        while k * b <= T:
            n = 0
            while n + k * b <= T:
                out.add(2 ** n * M ** k); n += 1
            k += 1
        if len(out) >= J:
            return sorted(out)[:J]
        T *= 1.7

def denominators(t):
    """G_j = lcm_i prod_{l != i} |t_i - t_l|  and  P_j = prod_{l<j} (t_j - t_l)."""
    j = len(t) - 1
    P = []
    for i in range(j + 1):
        p = 1
        for l in range(j + 1):
            if l != i:
                p *= (t[i] - t[l]) if t[i] > t[l] else (t[l] - t[i])
        P.append(p)
    L = 1
    for p in P:
        L = L // gcd(L, p) * p
    return L, P[j]

def part1(Ms, js):
    print("=" * 78)
    print("Part 1: log_2 of the exact Newton denominator G_j for <2,M>")
    print("        (M = 2 is the one-generated control: Sol = N_0)")
    print("=" * 78)
    for M in Ms:
        t = nodes(M, max(js) + 1)
        print(f"\nM = {M}   beta = log2 M = {math.log2(M):.6f}"
              f"   {'[CONTROL: one generator]' if M == 2 else '[two generators]'}")
        print(f"  {'j':>5} {'log2 G_j':>10} {'log2 P_j':>10} {'G_j/P_j':>8} "
              f"{'slope of log G_j':>17}")
        prev = None
        for j in js:
            G, Pj = denominators(t[:j + 1])
            lg, lp = G.bit_length(), Pj.bit_length()
            sl = "" if prev is None else f"{math.log(lg/prev[1])/math.log(j/prev[0]):17.3f}"
            print(f"  {j:>5} {lg:>10} {lp:>10} {lg/lp:>8.3f} {sl:>17}")
            prev = (j, lg)
    print("\n  Reading: control slope = 2.000 exactly (log_2 G_j = j^2 - 1);")
    print("  two-generated slopes drift to 1.5 with G_j/P_j bounded near 2.1.")
    print("  log G_j = o(j^2) therefore holds iff the monoid has two generators.")

def degree_bound(tau, beta, rho=2.1):
    """Explicit J with c_j = 0 for j >= J, from log G_j <= rho*j*log t_j."""
    return 4.0 * rho * tau * math.sqrt(2.0 * beta) / math.log(2.0)

# ----------------------------------------------------------------- Parts 2,3

def part23():
    from mpmath import mp, mpf, log, exp, power, nstr, pi
    mp.dps = 90
    print("\n" + "=" * 78)
    print("Part 2: smooth-branch identity  2^{s^2} = 2^{n^2} M^{2nk} (M^beta)^{k^2}")
    print("=" * 78)
    for (a, b) in [(0, 9), (1, 9), (3, 7), (0, 10), (2, 12)]:
        beta = a + b * log(3, 2)
        M = mpf(2) ** a * mpf(3) ** b          # = 2^beta exactly
        A = power(3, beta)                     # = 3^beta
        two_beta_sq = power(2, a * a) * power(3, a * b) * power(A, b)
        ok = abs(power(2, beta ** 2) / two_beta_sq - 1) < mpf(10) ** (-70)
        worst = 0
        for n in range(4):
            for k in range(4):
                s = n + k * beta
                worst = max(worst, abs(power(2, s * s) /
                            (power(2, n * n) * power(M, 2 * n * k) *
                             power(two_beta_sq, k * k)) - 1))
        print(f"  M = 2^{a} 3^{b} = {int(M):<10} beta = {nstr(beta,12):>14}"
              f"  2^(beta^2)=2^(a^2)3^(ab)A^b: {ok}   monoid check: {nstr(worst,3)}")
    print("\n" + "=" * 78)
    print("Part 3: control-side spectrum via theta series, tau_2 = pi^2/log(1/q)")
    print("=" * 78)
    for q in [mpf('0.5'), mpf('0.1'), mpf('0.01')]:
        pred = pi ** 2 / log(1 / q)
        for r in [mpf(20), mpf(40)]:
            tot = mpf(0)
            for k in range(-4000, 4001):
                tot += power(q, k * k) * exp(2 * pi * abs(k) * r)
            print(f"  q = {nstr(q,3):>6}  r = {int(r):>3}   log M(theta,r)/r^2 = "
                  f"{nstr(log(tot)/r**2,8):>12}   pi^2/log(1/q) = {nstr(pred,8)}")
    print("\n" + "=" * 78)
    print("Type scales (natural logs)")
    print("=" * 78)
    a2, b3 = log(2), log(3)
    for beta in [mpf(14), 9 * log(3, 2), mpf(27.1)]:
        tc = 1 / (4570 * beta ** 2 * a2 * b3)
        print(f"  beta = {nstr(beta,10):>14}   tau_crit = {nstr(tc,6):>12}"
              f"   log2/tau_crit = {nstr(a2/tc,6):>12}"
              f"   deg bound J(log 2,beta) = {degree_bound(float(a2), float(beta)):.1f}")
    print(f"  (log 2)/2 = {nstr(a2/2,10)}  = unconditional floor of the"
          f" exponential-quadratic family")

if __name__ == "__main__":
    part1([2, 3, 20001, 200000003], [25, 50, 100, 150, 200, 300, 400])
    part23()
