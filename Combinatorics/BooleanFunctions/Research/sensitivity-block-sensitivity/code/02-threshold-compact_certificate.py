#!/usr/bin/env python3
"""Verbatim reference certificate from Appendix A (standard library only)."""
if not __debug__:
    raise RuntimeError("Run without -O")
from math import comb

d, D, r, t, B, C = 16, 14_400_000_000, 4, 34, 30_000, 62_500
L, k, H = d + 2, 2 * D + 1, d + 1
S0 = [0] + [H - q + 1 for q in range(1, H + 1)]
S1 = [0] + [L * B - H + q for q in range(1, H + 1)]
J0 = [[0] * (H + 1) for _ in range(H + 1)]
J1 = [[0] * (H + 1) for _ in range(H + 1)]

def budget(a, b, c):
    return max((t-1)*a+b, (t-2)*a+b+c, (t-4)*a+3*c)

for level in range(1, d + 1):
    Q, H = H, H - 1
    a, target = S0[Q], r * S1[Q]
    s0, s1 = [0] * (H + 1), [0] * (H + 1)
    j0 = [[0] * (H + 1) for _ in range(H + 1)]
    j1 = [[0] * (H + 1) for _ in range(H + 1)]
    for q in range(1, H + 1):
        g = Q - q
        s0[q] = budget(a, S1[g], J1[g][Q])
        s1[q] = D * S0[g] + target
        for qp in range(q + 1, H + 1):
            gp = Q - qp
            j0[q][qp] = budget(a, J1[gp][g], J1[gp][Q])
            j1[q][qp] = D * J0[gp][g] + target
    for gap in range(1, H):
        for q in range(1, H - gap + 1):
            qp = q + gap
            for joint, single in ((j0, s0), (j1, s1)):
                u = min(joint[q][qp], single[q], single[qp])
                if gap > 1:
                    u = min(u, joint[q+1][qp], joint[q][qp-1])
                joint[q][qp] = u
    S0, S1, J0, J1 = s0, s1, j0, j1

A = max(C * S0[1], S1[1])
beta = C * B * k**d
W = L * r**d
n = beta * W
assert comb(k, t) < 2**1054 == r**(t*(t-3)//2)
assert A**50 < 2**14472
assert beta**50 > 2**29336
assert 1000*29336 - 2027*14472 == 1256
print(A, beta, W, n, sep="\n")
