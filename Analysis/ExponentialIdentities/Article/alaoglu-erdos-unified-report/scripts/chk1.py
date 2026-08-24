from sympy import factorint, primerange
from fractions import Fraction
import math

# ---------- (1) Does H2 ("K <= N/2") coincide with the script's `admissible` (7/12 < theta < 1)? ----------
def admissible_script(K, N):
    th = math.log(K)/math.log(N)
    return 7.0/12.0 < th < 1.0

M, A = 5, 11
N = A**7        # 19487171
K = M**10       # 9765625
print("N =", N, " K =", K, " N/2 =", N/2)
print("script-admissible:", admissible_script(K,N), " theta =", math.log(K)/math.log(N))
print("H2 upper half (K <= N/2):", K <= N//2)

# annulus for a single-cell slice: (N-K, N]; take a prime just above N-K
lo = N-K
print("N-K =", lo)
ps = list(primerange(lo+1, lo+400))
for p in ps[:6]:
    # v_p of descFactorial(N,K) = sum over y in (N-K, N] of v_p(y)
    v = 0
    mult = p
    while mult <= N:
        if mult > N-K:
            y = mult; e=0
            while y % p == 0: y//=p; e+=1
            v += e
        mult += p
    print("  p =", p, " p<=N/2:", p <= N//2, " v_p(descFact) =", v)
