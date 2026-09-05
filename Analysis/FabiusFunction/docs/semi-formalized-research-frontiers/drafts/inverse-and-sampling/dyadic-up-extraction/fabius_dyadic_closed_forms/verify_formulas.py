"""Exact, recurrence-free Fabius formulas and separate reference checks.
Python 3.10+; standard library only (determinant check uses exact Gaussian elimination).
"""
from fractions import Fraction as Q
from math import factorial as fac, comb
from itertools import combinations
from functools import lru_cache


def tm(a: int) -> int:
    if a < 0:
        raise ValueError('Thue-Morse index must be nonnegative')
    return -1 if a.bit_count() & 1 else 1


def compositions(k: int):
    """All ordered positive compositions, by cut subsets; no recurrence."""
    if k < 0:
        raise ValueError('k must be nonnegative')
    if k == 0:
        yield ()
        return
    for mask in range(1 << (k-1)):
        cuts = [0] + [j for j in range(1,k) if mask >> (j-1) & 1] + [k]
        yield tuple(v-u for u,v in zip(cuts,cuts[1:]))


def profiles(k: int):
    """Finite multiplicity profiles sum r*m_r=k, enumerated by a stack."""
    if k < 0:
        raise ValueError('k must be nonnegative')
    stack = [(1, k, ())]
    while stack:
        r, rem, p = stack.pop()
        if r > k:
            if rem == 0:
                yield p
            continue
        for m in range(rem // r + 1):
            stack.append((r+1, rem-r*m, p+(m,)))


def weak_compositions(k: int, N: int):
    if N == 0:
        if k == 0:
            yield ()
        return
    for bars in combinations(range(k+N-1), N-1):
        pts = (-1,) + bars + (k+N-1,)
        yield tuple(pts[j+1]-pts[j]-1 for j in range(N))


@lru_cache(None)
def b_comp(k: int) -> Q:
    """Normalized moment c_k/(2k)! from positive composition weights."""
    ans = Q(0)
    for rs in compositions(k):
        suffix = k
        term = Q(1)
        for r in rs:
            term /= fac(2*r+1) * (4**suffix-1)
            suffix -= r
        ans += term
    return ans


@lru_cache(None)
def bernoulli(m: int) -> Q:
    # B_1=-1/2; Python uses 0**0=1.
    return sum((Q(sum((-1)**j*comb(v,j)*j**m for j in range(v+1)),v+1)
                for v in range(m+1)), Q(0))


@lru_cache(None)
def beta(r: int) -> Q:
    if r < 1:
        raise ValueError('r must be positive')
    return Q(4**r, (4**r-1)*2*r*fac(2*r)) * bernoulli(2*r)


@lru_cache(None)
def b_part(k: int) -> Q:
    ans = Q(0)
    for ms in profiles(k):
        term = Q(1)
        for r,m in enumerate(ms,1):
            term *= beta(r)**m / fac(m)
        ans += term
    return ans


@lru_cache(None)
def alpha(k: int) -> Q:
    """Coefficient of t^(2k) in the reciprocal centered MGF."""
    ans = Q(0)
    for ms in profiles(k):
        term = Q(1)
        for r,m in enumerate(ms,1):
            term *= (-beta(r))**m / fac(m)
        ans += term
    return ans


def qp(q: Q, d: int) -> Q:
    z = Q(1)
    for r in range(1,d+1):
        z *= 1-q**r
    return z


def weights(d: int, q=Q(1,4)):
    return [Q((-1)**(d-j))*q**((d-j)*(d-j+1)//2) /
            (qp(q,j)*qp(q,d-j)) for j in range(d+1)]


@lru_cache(None)
def prefix_b(k: int, N: int) -> Q:
    ans = Q(0)
    for rs in weak_compositions(k,N):
        term = Q(1)
        for j,r in enumerate(rs,1):
            term /= 4**(j*r)*fac(2*r+1)
        ans += term
    return ans


@lru_cache(None)
def b_prefix(k: int) -> Q:
    return sum((w*prefix_b(k,j) for j,w in enumerate(weights(k))),Q(0))


def dyadic_bits(a: int, n: int, coeff=b_comp) -> Q:
    """Signed global Fabius at a/2**n. Nonnegative integer a,n."""
    if not isinstance(a,int) or not isinstance(n,int) or a<0 or n<0:
        raise ValueError('a,n must be nonnegative integers')
    ans=Q(0)
    for i in range(n+1):
        if not (a >> i) & 1:
            continue
        K=(1<<i) + 2*(a % (1<<i))
        v=sum((coeff(k)*4**(i*k)*Q(K**(n-i-2*k),fac(n-i-2*k))
               for k in range((n-i)//2+1)),Q(0))
        ans += tm(a>>(i+1))*2**(i*(i+1)//2)*v
    return ans / 2**(n*(n+1)//2)


def dyadic_tm(a: int, n: int, coeff=b_comp) -> Q:
    return sum((coeff(k)*Q(sum(tm(h)*(2*a-2*h-1)**(n-2*k)
                                  for h in range(a)), fac(n-2*k))
                for k in range(n//2+1)),Q(0)) / 2**(n*(n+1)//2)


def spline_at_dyadic(a: int, n: int, N: int) -> Q:
    """p_N(a/2^n-1), with N factors, for 0<=a<=2^n, N>=n+1."""
    if not (0 <= a <= 2**n and N >= n+1):
        raise ValueError('requires 0<=a<=2**n and N>=n+1')
    J=a*2**(N-n-1)
    S=sum(tm(h)*(a*2**(N-n)-2*h-1)**(N-1) for h in range(J))
    return Q(S, 2**(N*(N-1)//2)*fac(N-1))


def dyadic_spline(a: int, n: int, stride=1, start=None) -> Q:
    N=n+1 if start is None else start
    return sum((w*spline_at_dyadic(a,n,N+stride*j)
                for j,w in enumerate(weights(n//2,Q(1,4**stride)))),Q(0))


def dyadic_cube(a: int, n: int) -> Q:
    # Literal finite-uniform-prefix formula, using common degree d for every k.
    d=n//2
    b=[sum((w*prefix_b(k,j) for j,w in enumerate(weights(d))),Q(0))
       for k in range(d+1)]
    return dyadic_tm(a,n,lambda k:b[k])


def determinant(A):
    """Exact determinant for verification; the article also gives its finite Leibniz sum."""
    A=[[Q(x) for x in row] for row in A]
    ans=Q(1)
    for i in range(len(A)):
        j=next((j for j in range(i,len(A)) if A[j][i]),None)
        if j is None:
            return Q(0)
        if i!=j:
            A[i],A[j]=A[j],A[i]; ans=-ans
        p=A[i][i]; ans*=p
        for j in range(i+1,len(A)):
            f=A[j][i]/p
            for k in range(i+1,len(A)):
                A[j][k]-=f*A[i][k]
    return ans


def dyadic_det(a: int,n: int) -> Q:
    d=n//2
    T=[[0]*(d+1) for _ in range(d+1)]
    T[0][0]=1
    for i in range(1,d+1):
        T[i][i]=(2*i+1)*(4**i-1)
        for j in range(i):
            T[i][j]=-comb(2*i+1,2*j)
    v=[comb(n,2*k)*sum(tm(h)*(2*a-2*h-1)**(n-2*k) for h in range(a))
       for k in range(d+1)]
    A=[row+[int(i==0)] for i,row in enumerate(T)]+[v+[0]]
    D=2**(n*(n+1)//2)*fac(n)
    for i in range(1,d+1):
        D*=(2*i+1)*(4**i-1)
    return -determinant(A)/D


def fabius(x: Q) -> Q:
    x=Q(x)
    if x<=0:
        return Q(0)
    if x>=1:
        return Q(1)
    den=x.denominator
    if den&(den-1):
        raise ValueError('argument must be dyadic')
    return dyadic_bits(x.numerator, den.bit_length()-1)


def up(x: Q) -> Q:
    return fabius(1-abs(Q(x)))


def global_fabius(x: Q) -> Q:
    x=Q(x)
    if x<=0:
        return Q(0)
    den=x.denominator
    if den&(den-1):
        raise ValueError('argument must be dyadic')
    return dyadic_bits(x.numerator,den.bit_length()-1)


def reference_coeffs(K: int):
    # Isolated recurrence: used ONLY as a separately derived validation oracle.
    b=[Q(1)]
    for k in range(1,K+1):
        b.append(sum((b[j]/fac(2*(k-j)+1) for j in range(k)),Q(0))/(4**k-1))
    return b


def run_checks():
    import time
    start=time.time()
    bs=reference_coeffs(12)
    for k in range(13):
        assert b_comp(k)==bs[k]==b_part(k)
        assert sum(bs[j]*alpha(k-j) for j in range(k+1))==int(k==0)
    for k in range(7):
        assert b_prefix(k)==bs[k]
    for d in range(7):
        w=weights(d)
        for r in range(d+1):
            assert sum(w[j]*Q(1,4)**(j*r) for j in range(d+1))==int(r==0)
    count=0
    for n in range(10):
        for a in range(2**n+1):
            ref=dyadic_tm(a,n,lambda k:bs[k])
            assert dyadic_bits(a,n)==ref,(a,n,'bits')
            assert dyadic_spline(a,n)==ref,(a,n,'spline')
            assert dyadic_cube(a,n)==ref,(a,n,'cube')
            assert dyadic_bits(a*2,n+1)==ref,(a,n,'refine')
            assert ref+dyadic_bits(2**n-a,n)==1,(a,n,'reflection')
            if n<=6:
                assert dyadic_det(a,n)==ref,(a,n,'det')
            count+=1
    global_count=0
    for n in range(7):
        for a in range(3*2**n+1):
            ref=dyadic_tm(a,n,lambda k:bs[k])
            assert dyadic_bits(a,n)==ref,(a,n,'global')
            x=Q(a,2**n); block=int(x//2)
            assert ref==tm(block)*up(x-2*block-1),(a,n,'block')
            global_count+=1
    for n,a in [(2,1),(3,3),(4,5),(5,17),(6,29)]:
        f=dyadic_bits(a,n)
        assert dyadic_spline(a,n,stride=2)==f
        assert dyadic_spline(a,n,start=n+3)==f
        # Actual finite-prefix scale polynomial from reciprocal moments and exact derivatives.
        for N in [n+1,n+2,n+4]:
            poly=sum((alpha(r)*Q(1,4**(N*r))*2**(r*(2*r+1))*
                      dyadic_bits(a,max(n-2*r,0))
                      for r in range(n//2+1)),Q(0))
            assert poly==spline_at_dyadic(a,n,N),(a,n,N,'scale polynomial')
    print('PASS: normalized moments, 0<=k<=12 (composition, partition, reference).')
    print('PASS: finite-prefix moments, 0<=k<=6, and inverse-MGF coefficients.')
    print('PASS:',count,'bounded dyadic representations, 0<=n<=9:')
    print('  binary, Thue-Morse, spline, cube, refinement, reflection; determinant through n=6.')
    print('PASS:',global_count,'signed-global representations, 0<=n<=6, 0<=a<=3*2^n.')
    print('PASS: selected nonconsecutive spline prefixes and actual scale polynomials.')
    print('Elapsed seconds:',round(time.time()-start,3))
    print('\nNormalized/even moments:')
    for k in range(7): print(k,bs[k],bs[k]*fac(2*k),beta(k) if k else '-')
    print('\nValues at sixteenths (0<=a<=8):')
    for a in range(9): print(a,dyadic_bits(a,4))
    print('\nSmall spline examples:')
    for n,a in [(2,1),(3,3),(4,5)]:
        print(a,n,[str(spline_at_dyadic(a,n,n+1+j)) for j in range(n//2+1)],
              [str(w) for w in weights(n//2)],dyadic_bits(a,n))
    print('\nLarge examples:')
    for n,a in [(10,1),(12,173),(20,12345)]:
        print(a,n,dyadic_bits(a,n),float(dyadic_bits(a,n)))

if __name__=='__main__':
    run_checks()
