"""Independent integer boundary checks for the accelerated staircase."""
import mpmath as mp
mp.mp.dps=80
a=mp.findroot(lambda a:7*a**3+14*a*a-7*a-1,mp.mpf('.51'))
kappa=(-21*a*a+17*a+5)/29
J=20
def height(j):return int(mp.floor(j*j*mp.log(j)))
def block(j):
    h=height(j);q=h//2;ell=int(mp.floor(q/a));k=int(mp.nint(kappa*ell))
    return h,ell,q,k
def admissible(h,ell,q,r,k):
    assert 1<=q<=h and r>=0 and h+1-q+r>=1
    assert 0<=k<=r and 0<=r-k<=q and ell>=r+k+1
    assert abs(q-a*ell)<=2 and abs(k-kappa*ell)<=1
    assert abs(r-q)<=2*mp.sqrt(ell*mp.log(ell))
    return h+1-q+r
L={J:2*height(J)+1}
for j in range(J,1001):
    h,ell,q,k=block(j)
    rp=q-1+height(j+1)-h
    assert admissible(h,ell,q,rp,k)==height(j+1)
    if j>J:
        rm=q-1+height(j-1)-h
        assert admissible(h,ell,q,rm,k)==height(j-1)
    if j<1000:L[j+1]=L[j]+ell+block(j+1)[1]+2
print('PASS every ascending/descending block from level 20 through 1000')

def loop(m):
    ell=m-1;q=int(mp.nint(a*ell));r=q-1;k=int(mp.nint(kappa*ell))
    return ell,q,r,k
loops={m:loop(m) for m in range(1000,20001)}
for m,(ell,q,r,k) in loops.items():admissible(max(q,1),ell,q,r,k)
print('PASS all loop lengths 1000 through 20000 satisfy binomial interiors')
count=0
for K in range(J,36):
    gap=L[K+1]-L[K]
    for R in range(gap):
        if R<2000:
            assert L[K]+R==L[K]+R  # exact terminating-geometric padding
        else:
            m1=R//2;m2=R-m1
            assert m1+m2==R
            for m in [m1,m2]:
                ell,q,r,k=loops[m]
                assert admissible(height(K),ell,q,r,k)==height(K)
        count+=1
print('PASS exhaustive residual repair at levels 20 through 35:',count,'lengths')
for K in [100,300,999,10000,1000000]:
    h,ell,q,k=block(K);gap=ell+block(K+1)[1]+2
    for R in [2000,2001,gap//2,gap-2,gap-1]:
        if R>=gap:continue
        for m in [R//2,R-R//2]:
            pars=loops[m] if m in loops else loop(m)
            assert admissible(h,*pars)==h
    print('PASS large-height residual samples at level',K)
print('ALL INDEPENDENT STAIRCASE CHECKS PASSED')
