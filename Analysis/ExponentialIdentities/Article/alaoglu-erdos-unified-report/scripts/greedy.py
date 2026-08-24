from mpmath import mp, mpf, log, sqrt
mp.dps = 60

def stats(E):
    """Exact integer stats for greedy set {(i,j) in N0^2 : 2^i 3^j <= 2^E}."""
    q = 0; Si = 0; Sj = 0
    p3 = 1  # 3^j
    j = 0
    while True:
        # k_j = smallest k with 2^k >= 3^j
        k = (p3-1).bit_length()
        if k > E: break
        I = E - k          # max i
        n = I + 1
        q += n
        Si += I*(I+1)//2
        Sj += j*n
        j += 1
        p3 *= 3
    return q, Si, Sj

a = log(2); b = log(3)
target = log(6)/2
print("target log(6)/2 =", mp.nstr(target, 15))
prev=None
for E in [320,640,1280,2560,5120,10240]:
    q,Si,Sj = stats(E)
    mean = (Si*a + Sj*b)/q
    F = mpf(2)/3*sqrt(2*a*b*q) - mean
    d = target - F
    print(E, "q=%d"%q, "F=", mp.nstr(F,12), "gap=", mp.nstr(d,8), "gap*E=", mp.nstr(d*E,8))
