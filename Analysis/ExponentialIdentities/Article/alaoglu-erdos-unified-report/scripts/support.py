# EXACT: the greedy (minimal-frequency-sum) support is {(i,j): 2^i 3^j <= X}.
# q and the exponent sums Si=sum i, Sj=sum j are exact integers; Sum(lambda)=Si*log2+Sj*log3.
from mpmath import mp, log, sqrt, mpf
mp.dps = 40
a=log(2); b=log(3)
print(" X=2^E      q          Sum(lam)/q        (2/3)sqrt(2ab q)     ratio")
for E in [10,20,40,80,160,320,640,1280,2560,5120]:
    X = 2**E
    q=0; Si=0; Sj=0
    p3=1; j=0
    while p3<=X:
        # number of i with 2^i*p3<=X  -> i <= log2(X/p3)
        r = X//p3
        i=0; imax=-1
        v=1
        while v<=r:
            imax=i; i+=1; v*=2
        n=imax+1
        q+=n; Si+= imax*(imax+1)//2; Sj+= j*n
        j+=1; p3*=3
    lam = Si*a+Sj*b
    mean = lam/q
    asym = mpf(2)/3*sqrt(2*a*b*q)
    print("2^%-6d %-10d %-18s %-18s %s"%(E,q,mp.nstr(mean,10),mp.nstr(asym,10),mp.nstr(mean/asym,10)))
