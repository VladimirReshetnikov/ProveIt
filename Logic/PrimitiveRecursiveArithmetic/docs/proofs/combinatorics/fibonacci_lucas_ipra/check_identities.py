"""Finite regression checks; not proofs and not Lean/iPRA certification."""
from math import comb, gcd
N=45
F=[0,1]
L=[2,1]
for _ in range(2,3*N+5):
    F.append(F[-1]+F[-2]); L.append(L[-1]+L[-2])
checks=0
def verify(ok):
    global checks
    assert ok
    checks += 1
for n in range(1,N):
    verify(F[n+1]*F[n-1]-F[n]**2 == (-1)**n)
    verify(L[n]**2-5*F[n]**2 == 4*(-1)**n)
    verify(F[2*n]==F[n]*L[n])
    verify(L[2*n]==L[n]**2-2*(-1)**n)
    verify(sum(F[:n+1]) == F[n+2]-1)
    verify(sum(L[:n+1]) == L[n+2]-1)
    verify(sum(x*x for x in F[:n+1]) == F[n]*F[n+1])
    verify(sum((-1)**k * F[k+1] for k in range(n+1)) == 1 + (-1)**n*F[n])
    verify(sum((-1)**k * F[k] for k in range(n+1)) == (-1)**n*F[n-1]-1)
    verify(sum(comb(n,k)*F[k] for k in range(n+1))==F[2*n])
    verify(sum(comb(n,k)*F[k+1] for k in range(n+1))==F[2*n+1])
    verify(sum(comb(n,k)*L[k] for k in range(n+1))==L[2*n])
    verify(L[n+1]+L[n-1]==5*F[n])
    for r in range(n+1):
        verify(F[n]**2-F[n-r]*F[n+r]==(-1)**(n-r)*F[r]**2)
    for m in range(n,N):
        verify(F[m]*F[n+1]-F[m+1]*F[n]==(-1)**n*F[m-n])
        verify(L[m]*L[n]==L[m+n]+(-1)**n*L[m-n])
        verify(F[m]*L[n]==F[m+n]+(-1)**n*F[m-n])
    for m in range(1,N):
        verify(gcd(F[m],F[n])==F[gcd(m,n)])
for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
    verify(L[p]%p==1%p)
print(f"PASS: {checks} finite regression checks (not a proof)")
for n in range(N):
    verify(F[3*n]==F[n]*(L[n]**2-(-1)**n))
    verify(L[3*n]==L[n]**3-3*(-1)**n*L[n])
    verify(L[n]*F[n+1]-L[n+1]*F[n]==2*(-1)**n)
    verify(sum(L[k]**2 for k in range(n+1))==L[n]*L[n+1]+2)
    verify(sum(F[k]*L[k] for k in range(n+1))==F[2*n+1]-1)
    for m in range(n,N):
        verify(L[m]*F[n+1]-L[m+1]*F[n]==(-1)**n*L[m-n])
print('PASS: extra identities')
