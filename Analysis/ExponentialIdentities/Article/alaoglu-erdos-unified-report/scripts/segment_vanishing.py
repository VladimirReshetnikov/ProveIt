"""Forced initial-segment vanishing for small-type integer-valued functions on Sol.

Since N_0 is contained in Sol, the ordinary difference table Delta^k g(0) consists of
INTEGERS.  Cauchy on |z| = R with R = 2k (poles at 0..k) gives
    |Delta^k g(0)| <= M(g,2k) k! R/(R-k)^{k+1} = 2 M(g,2k) k!/k^k,
so  log|Delta^k g(0)| <= 4 tau k^2 - k + O(log k),  negative for k < 1/(4 tau).
An integer of modulus < 1 is zero; Newton on N_0 (binom(n,k) = 0 for k > n) propagates
this to g(n) = 0 for all n <= K = floor(1/(4 tau)).

At the self-contained threshold tau_crit = 1/(C beta^2 log2 log3), C = 4570, this is
K = (C ab/4) beta^2 = 870 beta^2 -- the same constant 870 as the vanishing-branch excess
factor, both being the ratio of the Jensen floor 1/(4 beta) to the threshold.
"""
import math

a, b = math.log(2), math.log(3)
C = 4570


def logbound(k, tau):
    """Rigorous bound on log|Delta^k g(0)| with contour radius R = 2k."""
    return tau * (2 * k) ** 2 - k + math.log(2 * math.sqrt(2 * math.pi * k))


if __name__ == "__main__":
    print("Rigorous bound  log|Delta^k g(0)| <= 4 tau k^2 - k + O(log k)   (R = 2k)")
    print(f"{'tau':>14} {'K = 1/(4 tau)':>15} {'bound at K/2':>15} {'bound at K':>13}")
    for tau in (1e-3, 1e-5, 1.4661e-6):
        K = 1 / (4 * tau)
        print(f"{tau:14.4e} {K:15.0f} {logbound(K/2, tau):15.1f} {logbound(K, tau):13.1f}")

    print(f"\nAt tau_crit = 1/({C} beta^2 log2 log3):")
    for beta in (14, 20, 27):
        tau = 1.0 / (C * beta * beta * a * b)
        print(f"   beta={beta:3}: tau_crit={tau:.4e}  ->  K = {1/(4*tau):,.0f} "
              f"= {C*a*b/4:.0f} * beta^2")
    print(f"\ncoefficient C*ab/4 = {C*a*b/4:.1f}  (= the vanishing-branch excess factor per beta)")
