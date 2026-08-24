from mpmath import mp, mpf, log, sqrt
mp.dps = 50
exec(open('greedy.py').read().split('a = log(2)')[0])
a=log(2); b=log(3); target=log(6)/2
print("E      F                gap*E        monotone?")
prevF=None
bad=0
for E in range(200,1201,1):
    q,Si,Sj = stats(E)
    F = mpf(2)/3*sqrt(2*a*b*q) - (Si*a+Sj*b)/q
    g = (target-F)*E
    if prevF is not None and F < prevF:
        bad+=1
        if bad<=12: print("NON-MONOTONE at E=%d: F(%d)=%s  F(%d)=%s"%(E,E-1,mp.nstr(prevF,12),E,mp.nstr(F,12)))
    prevF=F
print("total non-monotone steps in E=200..1200:", bad)
