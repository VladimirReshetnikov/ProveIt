from mpmath import mp, mpf, log, sqrt
mp.dps = 40
a = log(2); b = log(3)

def simplex_sum(q, i0=0):
    """sum of the q smallest values of i*a+j*b with i>=i0, j>=0 (exact-ish, high precision)."""
    # find L with N(L)>=q
    L = sqrt(2*a*b*q)*mpf('1.2')+10
    def count_and_sum(L):
        n=0; s=mpf(0)
        j=0
        while j*b <= L:
            rem = L - j*b
            # i from i0 to floor((rem - i0*a)/a)... value i*a+j*b <= L => i <= rem/a
            imax = int(mp.floor(rem/a + mpf('1e-30')))
            if imax >= i0:
                k = imax - i0 + 1
                n += k
                # sum_{i=i0}^{imax} (i a + j b) = a*(sum i) + k*j*b
                si = (imax*(imax+1) - (i0-1)*i0)//2
                s += a*si + k*j*b
            j += 1
        return n, s
    # bisect on L to get N(L) just >= q
    lo, hi = mpf(0), L
    for _ in range(200):
        mid = (lo+hi)/2
        n,_s = count_and_sum(mid)
        if n >= q: hi = mid
        else: lo = mid
    n, s = count_and_sum(hi)
    # n >= q ; the largest value(s) equal hi (ties). remove (n-q) copies of hi
    return s - (n-q)*hi

def f_min(q, C, H):
    """min over rho>1 of (H+R(rho))*C - ((q-1)/2)*log rho , R=(rho+1/rho-2)/4"""
    rho = ((q-1) + sqrt(mpf(q-1)**2 + C**2))/C
    R = (rho + 1/rho - 2)/4
    return (H+R)*C - (mpf(q-1)/2)*log(rho), rho, R

def qmin(H, G, i0=0):
    # bracket
    lo, hi = 2, 10
    while True:
        C = simplex_sum(hi, i0)/hi
        v,_,_ = f_min(hi, C, H)
        if v < G: break
        hi *= 2
    lo = hi//2
    while lo+1 < hi:
        mid = (lo+hi)//2
        C = simplex_sum(mid, i0)/mid
        v,_,_ = f_min(mid, C, H)
        if v < G: hi = mid
        else: lo = mid
    return hi

for H in [1000]:
    q0 = qmin(mpf(H), mpf(0))
    print(H, "G=0 :", q0)
