import numpy as np, math, sys
a = math.log(2); b = math.log(3)

def count_and_sum(L, i0=0):
    jm = int(L/b)
    j = np.arange(0, jm+1, dtype=np.float64)
    rem = L - j*b
    imax = np.floor(rem/a + 1e-12).astype(np.int64)
    k = imax - i0 + 1
    m = k > 0
    k = k[m]; imaxm = imax[m]; jm2 = j[m]
    n = int(k.sum())
    si = (imaxm*(imaxm+1) - (i0-1)*i0)//2
    s = float((a*si.astype(np.float64) + k*jm2*b).sum())
    return n, s

def simplex_sum(q, i0=0):
    lo, hi = 0.0, math.sqrt(2*a*b*max(q,1))*1.5 + 20
    for _ in range(80):
        mid = (lo+hi)/2
        n,_ = count_and_sum(mid, i0)
        if n >= q: hi = mid
        else: lo = mid
    n, s = count_and_sum(hi, i0)
    return s - (n-q)*hi

def f_min(q, C, H):
    rho = ((q-1) + math.sqrt((q-1)**2 + C**2))/C
    R = (rho + 1/rho - 2)/4
    return (H+R)*C - ((q-1)/2)*math.log(rho), rho, R

def feasible(q, H, G, i0=0):
    C = simplex_sum(q, i0)/q
    v,_,_ = f_min(q, C, H)
    return v < G

def qmin(H, G, i0=0):
    hi = 16
    while not feasible(hi, H, G, i0): hi *= 2
    lo = hi//2
    while lo+1 < hi:
        mid = (lo+hi)//2
        if feasible(mid, H, G, i0): hi = mid
        else: lo = mid
    return hi

H=1000.0
print("H=1e3 G=0:", qmin(H,0.0))

print("--- baselines G=0, i0=0 ---")
for H in [1e3,1e4,1e5]:
    print(H, qmin(H,0.0))
print("--- G=aH, NO support restriction (i0=0) : the claim's headline comparison ---")
for H in [1e3,1e4,1e5]:
    q0=qmin(H,0.0); q1=qmin(H,a*H)
    print(H, q0, q1, (q0-q1)/q0)
