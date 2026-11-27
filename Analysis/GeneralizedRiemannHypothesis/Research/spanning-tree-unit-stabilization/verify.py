"""Independent exact integer replay, no third-party packages."""
from itertools import product
from math import prod
from functools import lru_cache

def split(z,p):
    a=0
    while z%p==0:
        a+=1
        z//=p
    return a,z

def determinant(a):
    if not a:
        return 1
    old=1
    for k in range(len(a)-1):
        pivot=a[k][k]
        assert pivot>0
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                a[i][j],r=divmod(pivot*a[i][j]-a[i][k]*a[k][j],old)
                assert not r
            a[i][k]=0
        old=pivot
    return a[-1][-1]

def trees(vertices,steps,add):
    index={v:i for i,v in enumerate(vertices)}
    a=[[0]*(len(vertices)-1) for _ in vertices[:-1]]
    for i,x in enumerate(vertices):
        for s in steps:
            j=index[add(x,s)]
            if i==j:
                continue
            if i<len(a):
                a[i][i]+=1
            if j<len(a):
                a[j][j]+=1
            if i<len(a) and j<len(a):
                a[i][j]-=1
                a[j][i]-=1
    return determinant(a)

def semidirect(p,n,steps):
    q=p**n
    mul=lambda x,y:((x[0]+pow(1+p,x[1],q)*y[0])%q,(x[1]+y[1])%q)
    return trees(list(product(range(q),repeat=2)),steps,mul)

def flip2(n,steps): # Z_2^2 ⋊ (C_2 × C_2), flip the second coordinate
    q=2**n
    def mul(x,y):
        return ((x[0]+y[0])%q,(x[1]+(-1 if x[2]&1 else 1)*y[1])%q,x[2]^y[2])
    return trees(list(product(range(q),range(q),range(4))),steps,mul)

@lru_cache(None)
def cyclo_shell(p,h,r):
    q=p**(h-1)
    return sum((-r)**(j*q) for j in range(p))

def check_ratio(upper,lower,p,k):
    u=split(upper,p)[1]
    l=split(lower,p)[1]
    assert (u-l)%p**k==0 and (u-l)%p**(k+1)!=0
    return u%p**(k+1),l%p**(k+1)

if __name__=='__main__':
    for p,r in [(2,3),(3,5),(5,4),(7,6),(11,10)]:
        hs = range(2,10) if p==2 else range(1,5)
        for h in hs:
            x=split(cyclo_shell(p,h,r),p)[1]**2
            k=h+(p==2)
            assert split(x-1,p)[0]==k
    for p,r,h in [(2,3,3),(3,5,2),(5,4,2)]:
        q=p**h
        S=[1]*(r-1)**2+[2]*r
        c=trees(list(range(q)),S,lambda x,y:(x+y)%q)
        assert c==q*prod(cyclo_shell(p,j,r)**2 for j in range(1,h+1))
    print('24 exact cyclic layer checks and 3 independent cyclic cofactor checks.')
    for name,p,t,steps,k in [
        ('semidirect 81',3,lambda n,s:semidirect(3,n,s),[(1,0),(0,1),(1,1)],2),
        ('reflection 64',2,flip2,[(1,0,0),(0,1,0),(0,0,1),(0,0,2),(2,3,0)],3),
    ]:
        a,b=t(2,steps),t(1,steps)
        print(name, check_ratio(a,b,p,k))
    assert check_ratio(12,1,2,1)==(3,1) # three parallel voltage-loop pairs
    print('Binary level-one sharpness checked.')
