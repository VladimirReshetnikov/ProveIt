"""Exact interval certificate for the exponent-seven class-group bound.

The logarithm and the inverse square root use integer or Fraction enclosures.
Prints lower bounds after all split-prime charges, along with the upper log
of the discriminant on each interval used in the proof.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from bisect import bisect_right
from equal_norms import primes_to, FLOOR

GRID = 10**14
OLD = (21,14,10,6,4,1)
NEW = (1000,933,686,449,251,81)


def down(x):
    return x.numerator*GRID//x.denominator


def up(x):
    return -down(-x)


def unit_log(t):
    """Scale log(t) to GRID units for rational 1<=t<=2."""
    w=(t-1)/(t+1)
    assert 0<=w<=Q(1,3)
    terms=19
    value=2*sum(w**(2*j+1)/(2*j+1) for j in range(terms))
    tail=2*w**(2*terms+1)/((2*terms+1)*(1-w*w))
    return down(value),up(value+tail)


LOG2=unit_log(Q(2))


@lru_cache(None)
def log_bounds(n):
    k=n.bit_length()-1
    l,h=unit_log(Q(n,1<<k))
    return Q(k*LOG2[0]+l,GRID),Q(k*LOG2[1]+h,GRID)


@lru_cache(None)
def window(y,half):
    weights=half+tuple(-v for v in reversed(half))
    n=len(weights)
    norm=sum(a*a for a in weights)
    r=[Q(sum(weights[i]*weights[i+j] for i in range(n-j)),norm) for j in range(n+1)]
    ly,uy=log_bounds(y)
    lip=n*max(abs(a-b) for a,b in zip(r,r[1:]))/ly
    knots=[y**j for j in range(n+1)]
    low=down(2-Q(14,9)*lip)
    losses={}
    for p in primes_to(y):
        lp,hp=log_bounds(p)
        a,k=p,1
        while a<=y:
            j=bisect_right(knots,a**n)-1
            if j==n:
                assert a==y
                break
            delta=r[j+1]-r[j]
            f1=r[j]+delta*(n*k*lp/uy-j)
            f2=r[j]+delta*(n*k*hp/ly-j)
            root=isqrt(a*GRID*GRID)
            ends=[2*(-1)**k*f*l*t for f in (f1,f2) for l in (lp,hp)
                  for t in (Q(GRID,root),Q(GRID,root+1))]
            low+=down(min(ends))
            if k==1:
                losses[p]=max(0,up(2*max(ends)))
            a*=p;k+=1
    return low,losses


def groups(bmax,k):
    used=set()
    for b in range(1,bmax+1):
        if b in used:
            continue
        block={b*j for j in range(1,k+1) if b*j<=bmax}-used
        assert min(block)==b
        used.update(block)
        yield b
    assert len(used)==bmax


def format_down(units):
    return f'{units//GRID}.{units*1000//GRID%1000:03d}'


def format_up(units):
    ticks = -((-units * 1000) // GRID)
    return f'{ticks // 1000}.{ticks % 1000:03d}'


def verify(lower,upper,y,half,mult):
    base,w=window(y,half)
    if mult:
        assert lower>=FLOOR and y<694**2
        caps=[(isqrt(4*p**7//lower),v) for p,v in w.items()]
        largest=max(sz for sz,v in caps)
        assert (mult==1 and y<=6500) or (mult<=12 and y<=4200)
        cap=0
        for first in groups(largest,mult):
            cap+=max(v for sz,v in caps if sz>=first)
    else:
        assert lower==4*y**7
        cap=0
    rhs=base-cap
    upperlog=up(log_bounds(upper)[1])
    assert rhs>upperlog,(lower,upper,y,float(Q(rhs,GRID)),float(Q(upperlog,GRID)))
    print(lower,upper,y,mult,format_down(base),format_up(cap),
          format_down(rhs),format_up(upperlog))


def main():
    assert 4*691**7 < FLOOR < 4*701**7
    assert Q(49,20)-log_bounds(7)[1]>Q(1,2)
    assert log_bounds(31)[0]-log_bounds(10)[1]>Q(11,10)
    print('lower upper Y ratio_limit baseline_lower charge_upper forced_log_lower log_upper')
    upper=39*10**29
    for y in (7000,5000,4700,4600):
        lower=4*y**7
        verify(lower,upper,y,OLD,0)
        upper=lower
    for lower,y in ((4*10**22,6500),(10**22,4900)):
        verify(lower,upper,y,OLD,1);upper=lower
    # Test successively wider intervals from the lower end of the remaining gap.
    lower=FLOOR
    for numerator,denominator in ((105,100),(115,100),(130,100),(150,100),(180,100),(2,1),(3,1),(4,1)):
        if lower>=upper:
            break
        high=min(upper,lower*numerator//denominator)
        verify(lower,high,4200,NEW,12)
        lower=high
    assert lower==upper


if __name__=='__main__':
    main()
