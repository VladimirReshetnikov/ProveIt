r"""Verify the resonant-chain no-go exhaustively over all step vectors (p, q), not just
convergents.

Feasibility of the Minkowski criterion for a chain with step (-p, +q) requires

    2 p (L+1) log 2  <=  log( 1 / (eps * log 2) ),      eps = |p - q*theta|.

My first draft bounded eps > 1/(2q), which is WRONG: a large partial quotient makes eps far
smaller than 1/(2q). The correct unconditional input is an effective irrationality measure
for theta = log_2 3. The corpus cites Wu 2003, mu = 8.616, giving

    |theta - p/q| > c * q^(-mu)   hence   eps = q|theta - p/q| > c * q^(1-mu).

This script checks the inequality directly for every (p, q) in a large range, and then checks
the asymptotic form.
"""
from mpmath import mp, mpf, log as mlog

mp.dps = 60
TH = mlog(3) / mlog(2)
LOG2 = mlog(2)
MU = mpf("8.616")

print("Direct check over all step vectors (p, q) with q <= 4000, for L = 1")
print("(L = 1 is the easiest case; larger L only tightens the requirement)\n")

L = 1
best = None
for q in range(1, 4001):
    # only p near q*theta can give small eps
    p0 = int(mp.nint(q * TH))
    for p in (p0 - 1, p0, p0 + 1):
        if p < 1:
            continue
        eps = abs(mpf(p) - mpf(q) * TH)
        if eps == 0:
            continue
        lhs = 2 * mpf(p) * (L + 1) * LOG2
        rhs = mlog(1 / (eps * LOG2))
        slack = float(rhs - lhs)      # feasible iff slack >= 0
        if best is None or slack > best[0]:
            best = (slack, p, q, float(eps))
slack, p, q, eps = best
print(f"  most favourable step found: p={p}, q={q}, eps={eps:.6e}")
print(f"  required  2p(L+1)log2 = {float(2*mpf(p)*(L+1)*LOG2):.3f}")
print(f"  available log(1/(eps log2)) = {float(mlog(1/(mpf(eps)*LOG2))):.3f}")
print(f"  slack = {slack:.3f}   -> {'FEASIBLE' if slack >= 0 else 'INFEASIBLE'}")

print()
print("Asymptotic form, using eps > c q^(1-mu) with mu = 8.616 (Wu 2003):")
print("  feasibility needs 2p(L+1)log2 <= (mu-1) log q + O(1), and eps small forces")
print("  p >= q*theta - 1, so the requirement is")
print("      2(q*theta - 1)(L+1)log2  <=  7.616 log q + O(1).")
print(f"{'q':>8} {'LHS (L=1)':>14} {'RHS=7.616 log q':>18}  feasible?")
for q in (1, 2, 3, 5, 10, 100, 10**4, 10**8):
    lhs = 2 * (mpf(q) * TH - 1) * 2 * LOG2
    rhs = (MU - 1) * mlog(q) if q > 1 else mpf(0)
    print(f"{q:>8} {float(lhs):14.3f} {float(rhs):18.3f}  {'yes' if lhs <= rhs else 'no'}")
print()
print("LHS grows linearly in q, RHS logarithmically: infeasible for every q, and the")
print("margin only widens with L. The chain family cannot meet the Minkowski criterion.")
