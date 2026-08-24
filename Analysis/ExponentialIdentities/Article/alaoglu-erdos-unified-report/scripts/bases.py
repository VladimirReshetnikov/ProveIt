from mpmath import mp, mpf, log, sqrt, floor
mp.dps = 40
def run(u,v,Ls):
    a=log(u); b=log(v); tgt=(a+b)/2
    print("bases (%d,%d): predicted constant (a+b)/2 = log sqrt(%d) = %s"%(u,v,u*v,mp.nstr(tgt,12)))
    for L in Ls:
        q=0;Sl=mpf(0)
        j=0
        while j*b<=L:
            I=int(floor((L-j*b)/a))
            n=I+1
            q+=n
            Sl += a*mpf(I*(I+1)//2) + b*j*n
            j+=1
        F = mpf(2)/3*sqrt(2*a*b*q) - Sl/q
        print("   L=%-8s q=%-10d F=%s  (tgt-F)*sqrt(q)=%s"%(mp.nstr(L,6),q,mp.nstr(F,10),mp.nstr((tgt-F)*sqrt(q),6)))
    print()
run(2,3,[mpf(k) for k in (500,2000,8000)])
run(2,5,[mpf(k) for k in (500,2000,8000)])
run(3,7,[mpf(k) for k in (500,2000,8000)])
run(2,mp.e**mpf('1.7'),[mpf(k) for k in (500,2000,8000)]) if False else None
