from mpmath import mp, log, sqrt, mpf
mp.dps=40
a=log(2); b=log(3)
print("asym - exact mean, vs log(sqrt(6)) =", mp.nstr(log(6)/2,12))
for E in [320,640,1280,2560,5120,10240]:
    X=2**E; q=0;Si=0;Sj=0;p3=1;j=0
    while p3<=X:
        r=X//p3; i=0;imax=-1;v=1
        while v<=r: imax=i;i+=1;v*=2
        n=imax+1;q+=n;Si+=imax*(imax+1)//2;Sj+=j*n;j+=1;p3*=3
    mean=(Si*a+Sj*b)/q
    print("E=%-6d q=%-9d asym-mean = %s"%(E,q,mp.nstr(mpf(2)/3*sqrt(2*a*b*q)-mean,12)))
