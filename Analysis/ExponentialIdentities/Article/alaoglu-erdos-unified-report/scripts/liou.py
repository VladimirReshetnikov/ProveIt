from mpmath import mp, log, mpf, floor, nstr
mp.dps=40
# Mechanism C: integrality-Liouville.  x in S non-integer, n = nearest integer (n in S).
# |2^x - 2^n| >= 1  =>  ||x|| >= log(1+2^-n)/log2.   Base 2 is optimal among all bases g in S-outputs.
print("per-base exponent of the exclusion window (smaller base = stronger):")
for g in [2,3,6]:
    print("   base %d :  ||x|| >= log(1+%d^-n)/log %d  ~  %s * %d^-n"%(g,g,g,nstr(1/log(g),8),g))
print()
print("total measure of the excluded set over ALL k>=1, as a function of beta:")
for beta in [14,20,27,40]:
    b=mpf(beta)
    tot=2/log(2)*(2**(-b))/(1-2**(-b))
    print("   beta=%3d : sum_k 2*2^{-k beta}/log2 = %s"%(beta,nstr(tot,8)))
print()
print("Mechanism B: zero-free region delivered by a rank fraction f  (beta >= 1/((1-f)*kappa)):")
kappa=mpf('5.0872665807272117786')
for f in ['0','0.5','0.9','0.98595934','0.99271966']:
    f=mpf(f)
    print("   f=%-12s ->  beta >= %s"%(nstr(f,9),nstr(1/((1-f)*kappa),8)))
