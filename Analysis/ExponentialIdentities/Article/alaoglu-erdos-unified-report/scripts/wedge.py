import mpmath as mp, random, math, sys
from sympy import primerange

mp.mp.dps = 400

X = 10**5
PRIMES = [p for p in primerange(5, X)]
print("primes in [5,10^5):", len(PRIMES))

def qres(p, u):
    """Fermat quotient residue q_p(u) mod p, u coprime to p. Uses u mod p^2 only."""
    p2 = p*p
    return ((pow(u % p2, p-1, p2) - 1) // p) % p

def wedge(p, M, A, q2=None, q3=None):
    """Delta_p(M,A) = q_p(M) q_p(3) - q_p(A) q_p(2)  mod p. None if p | M*A."""
    if M % p == 0 or A % p == 0:
        return None
    if q2 is None: q2 = qres(p,2)
    if q3 is None: q3 = qres(p,3)
    return (qres(p,M)*q3 - qres(p,A)*q2) % p

# precompute q_p(2), q_p(3)
Q2 = {p: qres(p,2) for p in PRIMES}
Q3 = {p: qres(p,3) for p in PRIMES}

# sanity: Wieferich primes / double-Wieferich check
w2 = [p for p in PRIMES if Q2[p]==0]
w3 = [p for p in PRIMES if Q3[p]==0]
dbl = [p for p in PRIMES if Q2[p]==0 and Q3[p]==0]
print("Wieferich base2 in range:", w2)
print("Wieferich base3 in range:", w3)
print("double-Wieferich (2,3):", dbl)

# Mertens sums, exact rationals-ish (floats fine for reporting the heuristic, but
# compute with high precision)
S1 = mp.mpf(0); Slog = mp.mpf(0); theta = mp.mpf(0)
for p in [2,3]+PRIMES:
    S1 += mp.mpf(1)/p; Slog += mp.log(p)/p; theta += mp.log(p)
S1_5 = S1 - mp.mpf(1)/2 - mp.mpf(1)/3
print("sum_{p<10^5} 1/p           =", mp.nstr(S1, 12))
print("sum_{5<=p<10^5} 1/p        =", mp.nstr(S1_5, 12), "   <-- expected # of rank-drop primes per pair")
print("sum_{p<10^5} log p / p     =", mp.nstr(Slog, 12))
print("theta(10^5) = sum log p    =", mp.nstr(theta, 12))
print("pi(10^5) (p>=5)            =", len(PRIMES))
