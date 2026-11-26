"""Refine the finite CM support test with outward-rounded integer intervals."""
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial, gcd, isqrt, prod
from pathlib import Path
import sys

S = 10**36
PI = 3141592653589793238
PI_DEN = 10**18
K = 16


def ceildiv(a, b):
    return -(-a // b)


def add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def neg(x):
    return (-x[1], -x[0])


def scale(x, n):
    return (x[0]*n, x[1]*n)


def mul(x, y):
    products = [a*b for a in x for b in y]
    return min(products)//S, ceildiv(max(products), S)


def square(x):
    lo = 0 if x[0] <= 0 <= x[1] else min(x[0]**2, x[1]**2)//S
    return lo, ceildiv(max(x[0]**2, x[1]**2), S)


def div_pos(x, y):
    assert x[0] >= 0 and y[0] > 0
    return x[0]*S//y[1], ceildiv(x[1]*S, y[0])


def power(x, n):
    assert x[0]>=0
    return x[0]**n//S**(n-1), ceildiv(x[1]**n, S**(n-1))


ONE=(S,S)
ZERO=(0,0)


@lru_cache(None)
def exp_radius(D,a):
    # Return an enclosure for exp(pi*sqrt(D)/a).
    root=isqrt(D*S*S)
    lo=root*PI//(a*PI_DEN)
    hi=ceildiv((root+1)*(PI+1),a*PI_DEN)
    N=2**36
    assert 0 <= hi < N*S
    v = S+lo//N, ceildiv(S*S*N,S*N-hi)
    for _ in range(36):
        v=square(v)
    return v


@lru_cache(None)
def phase(a,b):
    # Taylor polynomials through degree 50, with Taylor remainder at most 4^51/51!.
    x=(S*b*PI//(a*PI_DEN), ceildiv(S*b*(PI+1), a*PI_DEN))
    sn, cs, term = ZERO, ONE, ONE
    for j in range(1,51):
        term=mul(term,x)
        term=term[0]//j, ceildiv(term[1],j)
        summand=neg(term) if j%4 in (2,3) else term
        if j%2:
            sn=add(sn,summand)
        else:
            cs=add(cs,summand)
    error=ceildiv(S*4**51, factorial(51))
    return add(cs,(-error,error)), add(sn,(-error,error))


def cmul(z,w):
    return (add(mul(z[0],w[0]),neg(mul(z[1],w[1]))),
            add(mul(z[0],w[1]),mul(z[1],w[0])))


def norm_squared(z):
    return add(square(z[0]),square(z[1]))


SIGMA3 = [sum(d**3 for d in range(1,n+1) if n%d==0) for n in range(K+1)]


def modulus_squared(D,a,b):
    E=exp_radius(D,a)
    if D >= 100*a*a:
        return square((E[0]-2079*S,E[1]+2079*S))
    r=div_pos(ONE,E)
    cs,sn=phase(a,b)
    q=mul(r,cs),mul(r,sn)
    qp=(ONE,ZERO)
    e4=[ONE,ZERO]
    product=ONE
    for n in range(1,K+1):
        qp=cmul(qp,q)
        for i in (0,1):
            e4[i]=add(e4[i],scale(qp[i],240*SIGMA3[n]))
        product=mul(product,norm_squared((add(ONE,neg(qp[0])),qp[1])))
    # |q| <= exp(-pi sqrt(3)) < 1/200 and sigma_3(n) < 2 n^3.
    tail=ceildiv(960*S*(K+1)**3,200**(K+1))
    e4=[add(x,(-tail,tail)) for x in e4]
    approx=div_pos(power(norm_squared(e4),3),power(product,24))
    # The logarithm of the missing factor prod |1-q^n|^(-48) in |j|^2
    # has absolute value <= 192 / 200^(K+1). For t<=1/2,
    # exp([-t,t]) is contained in [1-2t,1+2t].
    t=ceildiv(384*S,200**(K+1))
    return mul(mul(square(E),approx),(S-t,S+t))


def forms(D):
    for a in range(1,isqrt(D//3)+1):
        for b in range(D%2,a+1,2):
            c,rem=divmod(D+b*b,4*a)
            if rem==0 and a<=c and gcd(gcd(a,b),c)==1:
                yield a,b,c


def four_separated(intervals):
    high=None
    chosen=0
    for lo,hi in sorted(intervals,key=lambda r:r[1]):
        if high is None or lo>16*high:
            high=hi
            chosen+=1
    return chosen>=4


PERMS = list(permutations(range(4)))[1:]

def four_determinant(intervals):
    bounds=sorted((isqrt(lo*S),isqrt(hi*S)+1) for lo,hi in intervals)
    for rows in combinations(bounds,4):
        if any(rows[i][1]>=rows[i+1][0] for i in range(3)):
            continue
        lower=prod(lo**i for i,(lo,hi) in enumerate(rows))
        terms=[[hi**j for j in range(4)] for lo,hi in rows]
        upper=0
        for perm in PERMS:
            upper+=prod(terms[i][perm[i]] for i in range(4))
            if upper>=lower:
                break
        else:
            return True
    return False

def main():
    path=Path(sys.argv[1])
    pending=[]
    by_separation=by_determinant=by_sign=0
    for line in path.read_text().splitlines():
        D,h,*av=map(int,line.split())
        fs=list(forms(D))
        assert sorted(set(a for a,b,c in fs))==av
        assert sum(1 if b==0 or b==a or a==c else 2 for a,b,c in fs)==h
        intervals=[modulus_squared(D,a,b) for a,b,c in fs]
        if four_separated(intervals):
            by_separation+=1
        elif four_determinant(intervals):
            by_determinant+=1
        elif max(sum(b==0 or a==c for a,b,c in fs),
                 sum(b==a and a<c for a,b,c in fs))>=4:
            by_sign+=1
        else:
            pending.append((D,h))
    print("refined separation",by_separation,"determinant",by_determinant,"Descartes",by_sign,
          "unresolved",len(pending),"max",max(D for D,h in pending),file=sys.stderr)
    for D,h in pending:
        print(D,h)


if __name__=="__main__":
    main()
