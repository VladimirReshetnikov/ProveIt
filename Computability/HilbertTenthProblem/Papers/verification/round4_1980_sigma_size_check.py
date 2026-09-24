"""Sanity checks for the repair 80-R4-S1 of the satellite article
(Papers/1980/jones1980_theorem5_operations.tex, proof of the theorem
"x in W iff Sigma is solvable").

The original proof took the hypothesis n <= r of Lemma 2.26 (1982) from the
block bounds 0 <= S_i, T_i of the 1982 paper, whose derivation of 0 <= S_3
uses x b^5 <= q, i.e. the eliminated equation (E0) q = b^(5^60).  The repair
uses instead the factorization r = (n-1)(Sn + (T+1)(n+1)) of (E7) together
with 0 < T < n.  This script checks:

1. that (E2) alone, lambda (b^5 - 1) = q^4 - 1, has solutions with
   b < q < b^5, so that q > x b^5 cannot be recovered from (E1)-(E2);
2. the factorization of (E7);
3. that the second factor equals 1 exactly when n divides T;
4. 0 < T < q^16 on random instances satisfying only the inequalities that
   the repaired proof uses (theta*lambda < q^4, l < q^2, b < q, q > b^4.5).

Run with:  PYTHONUTF8=1 python round4_1980_sigma_size_check.py
"""
import random
import sympy as sp

# 1. (E2) alone admits b < q < b^5: fourth roots of unity mod b^5 - 1.
found = []
for b in range(2, 13):
    m = b**5 - 1
    for q in range(b + 1, b**5):
        if pow(q, 4, m) == 1:
            found.append((b, q))
            break
print("solutions of (E2) with b < q < b^5 (first per b):", found)
assert len(found) == 11
assert pow(6532, 4, 6**5 - 1) == 1 and 6**4.5 < 6532 < 6**5

# 2. Factorization of (E7).
S, T, n = sp.symbols('S T n')
r = S*(n**2 - n) + (T + 1)*(n**2 - 1)
assert sp.expand(r - (n - 1)*(S*n + (T + 1)*(n + 1))) == 0
print("factorization r = (n-1)(Sn + (T+1)(n+1)): ok")

# 3. The second factor equals 1 iff n | T.
for nn in range(2, 40):
    for TT in range(0, 3*nn):
        solvable = ((1 - (TT + 1)*(nn + 1)) % nn == 0)   # exists S with S*nn + (TT+1)(nn+1) = 1
        assert solvable == (TT % nn == 0), (nn, TT)
print("second factor = 1 iff n | T: ok")

# 4. 0 < T < q^16 on random instances.
random.seed(1)
for _ in range(2000):
    b = random.randint(3, 9)
    z = random.randint(1, (b - 1)//2)
    q = random.randint(int(b**4.5) + 1, b**5 + 50)
    theta = b**5 - 2*z
    lam = random.randint(1, (q**4 - 1)//theta)        # only theta*lambda < q^4 is used
    l = random.randint(1, q**2 - 1)                    # only l < q^2 is used
    T = q**3 - b*l + l + theta*lam*q**3 + (b**5 - 2)*q**8
    assert 0 < T < q**16, (b, q, l, lam)
print("0 < T < q^16 on 2000 random instances: ok")
print("ALL CHECKS PASSED")
