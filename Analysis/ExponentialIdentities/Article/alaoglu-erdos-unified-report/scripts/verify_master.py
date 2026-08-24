# Exact verification of the master Legendre identity for descFactorial,
# and of the Abel summation identity used in Theorem B.
import random
from math import gcd

def vp_fact(N, p):
    s = 0
    q = p
    while q <= N:
        s += N // q
        q *= p
    return s

def vp_desc(N, K, p):
    """v_p( (N)_K ) exactly."""
    return vp_fact(N, p) - vp_fact(N - K, p)

def sdig(n, b):
    t = 0
    while n:
        t += n % b
        n //= b
    return t

def vp_desc_legendre(N, K, p):
    num = K + sdig(N - K, p) - sdig(N, p)
    assert num % (p - 1) == 0, (N, K, p, num)
    return num // (p - 1)

# 1. master identity check
random.seed(1)
bad = 0
for _ in range(4000):
    N = random.randint(1, 20000)
    K = random.randint(0, N)
    p = random.choice([2,3,5,7,11,13,17,101,997,7919])
    a = vp_desc(N,K,p); b = vp_desc_legendre(N,K,p)
    if a != b:
        bad += 1; print("MISMATCH", N,K,p,a,b)
print("master identity: checked 4000 random (N,K,p); mismatches =", bad)

# also check directly against the literal falling factorial for small cases
def desc(N,K):
    r = 1
    for t in range(K): r *= (N-t)
    return r
bad2=0
for N in range(0, 60):
    for K in range(0, N+1):
        v = desc(N,K)
        for p in [2,3,5,7,11,13]:
            e = 0
            w = v
            while w % p == 0:
                w //= p; e += 1
            if e != vp_desc_legendre(N,K,p):
                bad2+=1; print("BAD",N,K,p,e,vp_desc_legendre(N,K,p))
print("direct factorization check on all 0<=K<=N<60, p<=13: mismatches =", bad2)

# 2. Abel identity: sum_l c_l M^{i_l} = sum_k T_k (M^{i_k} - M^{i_{k-1}}), M^{i_0}:=0
bad3 = 0
for _ in range(3000):
    M = random.randint(2, 40)
    s = random.randint(1, 6)
    idx = sorted(random.sample(range(0, 12), s))
    c = [random.randint(-9, 9) for _ in range(s)]
    lhs = sum(c[l] * M**idx[l] for l in range(s))
    T = [sum(c[l] for l in range(k, s)) for k in range(s)]
    prev = 0
    rhs = 0
    for k in range(s):
        rhs += T[k] * (M**idx[k] - prev)
        prev = M**idx[k]
    if lhs != rhs:
        bad3 += 1; print("ABEL BAD", M, idx, c, lhs, rhs)
print("Abel identity: checked 3000 random slices; mismatches =", bad3)
