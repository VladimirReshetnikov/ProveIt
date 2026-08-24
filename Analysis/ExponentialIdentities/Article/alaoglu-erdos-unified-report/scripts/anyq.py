from mpmath import mp, mpf, log, sqrt
mp.dps = 40
a=log(2); b=log(3); target=log(6)/2
# build ALL (i,j) with i*a+j*b <= Lmax, sorted by lambda, using exact comparison 2^i 3^j
Lmax = 700*a
import heapq
pts=[]
j=0; p3=1
while j*b <= Lmax:
    imax = int(mp.floor((Lmax - j*b)/a))+2
    for i in range(0, imax+1):
        if i*a + j*b <= Lmax: pts.append((i,j))
    j+=1; p3*=3
# exact sort key: compare 2^i 3^j as integers
pts.sort(key=lambda t: (t[0]*a+t[1]*b))
# verify sort is exact via integer comparison on neighbours
ok=all( (2**pts[k][0])*(3**pts[k][1]) <= (2**pts[k+1][0])*(3**pts[k+1][1]) for k in range(len(pts)-1))
print("exact-sort consistent:", ok, " total pts:", len(pts))
Si=0;Sj=0
res=[]
for n,(i,j) in enumerate(pts, start=1):
    Si+=i; Sj+=j
    if n>=1000:
        F = mpf(2)/3*sqrt(2*a*b*n) - (Si*a+Sj*b)/n
        res.append((n,F))
import random
print("\n arbitrary q (min-Sigma-lambda support of size exactly q):")
for n,F in res[::max(1,len(res)//12)]:
    print("  q=%-9d F=%s   (target-F)*sqrt(q)=%s"%(n, mp.nstr(F,12), mp.nstr((target-F)*sqrt(n),8)))
# max deviation over the tail
tail=[(abs(target-F),n) for n,F in res if n>50000]
tail.sort()
print("\n largest |target-F| for q>50000:", mp.nstr(tail[-1][0],8), "at q=",tail[-1][1])
print(" smallest:", mp.nstr(tail[0][0],8), "at q=",tail[0][1])
