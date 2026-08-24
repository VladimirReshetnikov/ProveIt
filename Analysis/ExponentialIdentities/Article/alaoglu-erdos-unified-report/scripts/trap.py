from mpmath import mp, mpf, log, cosh, sinh, tanh, sqrt, findroot, exp
mp.dps = 50
a = log(2); b = log(3)

# 1. reproduce kappa_* and the rank thresholds
t0 = findroot(lambda t: t*tanh(t)-2, mpf('2.0'))
kappa = 64*a*b*cosh(t0)/(9*t0**2)
print("t0            =", t0)
print("t0*tanh t0    =", t0*tanh(t0))
print("kappa_*       =", kappa, "   (report: 5.08726658)")
print("32ab/9        =", 32*a*b/9, "   (report: 2.70755559)")
for beta in [14, 27]:
    print("  beta=%2d  needed rank fraction 1-1/(kappa*beta) = %s"%(beta, mp.nstr(1-1/(kappa*beta), 8)))
print("  delta_*/H  = 2/cosh(t0) =", mp.nstr(2/cosh(t0),8))
