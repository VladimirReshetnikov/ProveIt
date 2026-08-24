from mpmath import mp, log, sqrt, cosh, mpf, findroot, tanh
mp.dps=30
a=log(2); b=log(3); c6=log(6)/2

# mean frequency of the greedy support of size q (exact asymptotic, verified numerically)
def meanlam(q): return mpf(2)/3*sqrt(2*a*b*q) - c6

# feasibility: (H + (delta/2)(1+cosh t)) * q*meanlam(q)  <  q(q-1)/2 * t + q*G
def feasible(q,H,delta,t,G):
    if q<2: return False
    R=(delta/2)*(1+cosh(t))
    return (H+R)*meanlam(q) < (q-1)/mpf(2)*t + G

def qmin(H,delta,G,disc=True):
    """smallest q for which some t makes the trap feasible"""
    def ok(q):
        # optimize t: scan geometrically
        lo,hi=mpf('0.01'),mpf(1)+2*log(4*(H+1)/delta)
        best=False
        n=400
        for i in range(n+1):
            t=lo+(hi-lo)*i/n
            if feasible(q,H,delta,t,G): return True
        return False
    lo,hi=2,4
    while not ok(hi): hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if ok(mid): hi=mid
        else: lo=mid
    return hi

t0=findroot(lambda t:t*tanh(t)-2,mpf(2)); kappa=64*a*b*cosh(t0)/(9*t0**2)
print("=== unit block delta=1 ===")
print("  H      q_min(G=0)   asym 32ab/9 H^2/(logH)^2   q_min(G=aH)   rel.gain   cond.count H/14")
for H in [mpf(100),mpf(1000),mpf(10000),mpf(100000)]:
    q0=qmin(H,mpf(1),mpf(0))
    asym=32*a*b/9*H**2/log(H)**2
    G=a*H                       # most favourable external prime: M=p^e, k_0=K=H/beta
    q1=qmin(H,mpf(1),G)
    print("  %-7s %-12d %-24s %-13d %-10s %s"%(mp.nstr(H,6),q0,mp.nstr(asym,8),q1,
          mp.nstr(mpf(q0-q1)/q0,4), mp.nstr(H/14,6)))

print()
print("=== macroscopic window delta = 2H/cosh(t0) ===")
print("  H       q_min(G=0)    kappa*H*delta      cond.count      deficiency q/count")
for H in [mpf(1000),mpf(10000),mpf(100000)]:
    d=2*H/cosh(t0)
    q0=qmin(H,d,mpf(0))
    pred=kappa*H*d
    cnt=d*(H+d/2)/14
    print("  %-8s %-13d %-18s %-15s %s"%(mp.nstr(H,6),q0,mp.nstr(pred,8),mp.nstr(cnt,8),mp.nstr(mpf(q0)/cnt,6)))
