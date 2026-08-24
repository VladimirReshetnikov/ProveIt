"""Do the SHORT (non-mesoscopic) annuli actually contain primes?  If they do in practice,
the residual gap in Theorem A is purely a prime-supply technicality, not a structural one."""
from math import log
M,A,n,m=5,11,3,3
def sieve(X):
    s=bytearray([1])*(X+1); s[0]=s[1]=0
    for i in range(2,int(X**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return s
K=[M**(n+i) for i in range(5)]; N=[A**(m+j) for j in range(3)]
sv=sieve(max(N))
print(f"{'slice':>6} {'levels':>22} {'k':>2} {'annulus':>28} {'len':>7} {'N^7/12':>9} {'#primes':>8} {'meso':>5}")
for j in range(3):
    lv=[i for i in range(5) if K[i]<=N[j]]
    for k in range(len(lv)):
        lo=N[j]-K[lv[k]]; hi=N[j]-(K[lv[k-1]] if k>0 else 0)
        L=hi-lo
        npr=sum(1 for p in range(lo+1,hi+1) if sv[p])
        thr=N[j]**(7/12)
        print(f"{j:>6} {str([K[i] for i in lv]):>22} {k:>2} ({lo:>10},{hi:>10}] {L:>7} {thr:>9.0f} {npr:>8} {str(L>=thr):>5}")
