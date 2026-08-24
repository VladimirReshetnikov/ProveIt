from mpmath import mp, log, sqrt, cosh, mpf
mp.dps=30
a=log(2); b=log(3); c6=log(6)/2

def qmin(H,delta,G,corr,i0=0):
    """corr: subtract log sqrt6 (exact discrete support) or not.  i0: monomial floor i>=i0."""
    def ml(q):
        m=mpf(2)/3*sqrt(2*a*b*q)
        if corr: m-=c6
        return m + i0*a
    def ok(q):
        if q<2: return False
        hi=mpf(1)+2*log(4*(H+1)/delta); n=400
        for i in range(n+1):
            t=mpf('0.01')+(hi-mpf('0.01'))*i/n
            R=(delta/2)*(1+cosh(t))
            if (H+R)*ml(q) < (q-1)/mpf(2)*t + G: return True
        return False
    lo,hi=2,4
    while not ok(hi): hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if ok(mid): hi=mid
        else: lo=mid
    return hi

print("delta=1.  Gain from lattice DISCRETENESS (control-blind) vs from the EXTERNAL PRIME (control-clean)")
print("  H       q(cont,G=0)   q(disc,G=0)   q(disc,G=aH)   gain_discrete  gain_extprime   ratio")
for H in [mpf(1000),mpf(10000),mpf(100000)]:
    qc=qmin(H,mpf(1),mpf(0),False)
    qd=qmin(H,mpf(1),mpf(0),True)
    qg=qmin(H,mpf(1),a*H,True)
    print("  %-8s %-13d %-13d %-14d %-14d %-14d %s"%(mp.nstr(H,6),qc,qd,qg,qc-qd,qd-qg,mp.nstr(mpf(qc-qd)/max(1,qd-qg),5)))

print()
print("Monomial floor i>=i0 with the MAXIMAL matching external-prime gain G=i0*a*H:")
print("  H=10^4:  i0     q_min      (i0=0 baseline shown first)")
H=mpf(10000)
for i0 in [0,1,2,4,8]:
    print("           %-6d %d"%(i0,qmin(H,mpf(1),i0*a*H,True,i0)))
