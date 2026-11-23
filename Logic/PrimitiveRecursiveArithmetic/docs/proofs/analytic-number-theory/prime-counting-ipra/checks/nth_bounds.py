"""Directed integer interval checks for the nth-prime inequalities. Run with Python 3."""
from math import isqrt
from finite_bounds import SCALE as S, sieve, integer_log, cells
from certify_li import log_interval

END = 1_000_000
RULES = (
    (1, 'lower', 'Rosser log'), (6, 'upper', 'Rosser log + loglog'),
    (2, 'lower', 'Dusart -1'), (20, 'upper', 'Rosser -0.5'),
    (39017, 'upper', 'Dusart -0.9487'),
    (3, 'lower', 'Dusart second 2.1'), (688383, 'upper', 'Dusart second 2'),
    (2, 'lower', 'Axler 11.321'), (2, 'lower', 'Axler simplified'),
    (3468, 'upper', 'Axler 0'), (46254381, 'upper', 'Axler 10.667'),
)


def ceil_div(a, b):
    return -((-a)//b)


def divide(lo, hi, d, e):
    """Enclose [lo,hi]/[d,e] on the fixed-point grid, with d>0."""
    assert 0 < d <= e
    return lo*S//(e if lo >= 0 else d), ceil_div(hi*S, d if hi >= 0 else e)


def log_pair(n, fine):
    if fine:
        l, h = log_interval(n)
        w, z = log_interval(l)[0], log_interval(h)[1]
        return int(l*S), ceil_div(h.numerator*S, h.denominator), (w*S).__floor__(), (z*S).__ceil__()
    l, h = integer_log(n)
    a, b = cells[-1]
    w = integer_log(l)[0] - 52*b
    z = integer_log(h)[1] - 52*a
    return l, h, w, z


def bounds(n, fine=False, opposite=False):
    l, h, w, z = log_pair(n, fine)
    blo, bhi = l+w-S, h+z-S
    corrlo, corrhi = divide(w-2*S, z-2*S, l, h)
    flo, fhi = blo+corrlo, bhi+corrhi
    def axler(c, simple=False):
        # Rewrite the quadratic as (w-3)^2 + c - 9; c is in thousandths.
        left, right = (w,z) if simple else (w-3*S,z-3*S)
        low_sq = 0 if left <= 0 <= right else min(left**2,right**2)
        high_sq = max(left**2,right**2)
        offset = 0 if simple else c-9000
        a, b = divide(1000*low_sq+offset*S*S, 1000*high_sq+offset*S*S,
                      2000*l*l, 2000*h*h)
        return flo-b, fhi-a
    if opposite:
        return [l, h+z, blo, bhi+S//2, bhi+ceil_div(513*S,10000),
                blo + divide(10*w-21*S,10*z-21*S,10*l,10*h)[0],
                fhi, axler(11321)[0], axler(0,True)[0], axler(0)[1], axler(10667)[1]]
    return [h, l+w, bhi, blo+S//2, blo+(513*S)//10000,
            bhi + divide(10*w-21*S,10*z-21*S,10*l,10*h)[1],
            flo, axler(11321)[1], axler(0,True)[1], axler(0)[0],
            axler(10667)[0]]


def quotient_count(n):
    """Sieve on the distinct floor quotients, as in prime_table.cpp."""
    r = isqrt(n)
    keys = [n//i for i in range(1,r+1)]
    keys.extend(range(keys[-1]-1,0,-1))
    count = {v:v-1 for v in keys}
    for p in range(2,r+1):
        before = count[p-1]
        if count[p] == before:
            continue
        for v in keys:
            if v < p*p:
                break
            count[v] -= count[v//p]-before
    return count[n]


def main():
    flags = sieve(16_000_000)
    primes = (p for p in range(2,len(flags)) if flags[p])
    assert next(primes) == 2  # n=1: p_1=2 > 1*log(1)=0.
    failures = {name:[] for _,_,name in RULES}
    for n in range(2,END+1):
        p = next(primes)
        estimates = bounds(n)
        fine = None
        for i, (start, side, name) in enumerate(RULES):
            if n < start:
                continue
            def passes(est):
                return p*S > n*est[i] if side == 'lower' else p*S < n*est[i]
            if not passes(estimates):
                if fine is None:
                    fine = bounds(n,True)
                if not passes(fine):
                    endpoint = bounds(n,True,True)[i]
                    assert (p*S < n*endpoint if side=='lower' else p*S > n*endpoint), (name,n,p)
                    failures[name].append((n,p,(min(fine[i],endpoint)*n)//S,
                                              ceil_div(max(fine[i],endpoint)*n,S)))
    assert p == 15485863
    for start, side, name in RULES[:-1]:
        bad=failures[name]
        print(f'{name} ({side}), {start}..{END}: failures = {len(bad)}.')
        if bad:
            print('  (index, prime, lower and upper integer bounds for the comparison expression)')
            print(' ',bad)
    assert [(name,row) for name,rows in failures.items() for row in rows] == [
        ('Dusart -0.9487',(39017,467473,467471,467472))]
    l,h,w,z = log_pair(39017,True)
    assert 467471 * 10000*S < 39017*(10000*(l+w)-9487*S)
    assert 39017*(10000*(h+z)-9487*S) < 467472*10000*S
    assert 467473*10000*S < 39017*(10000*(l+w)-9484*S)
    print('Published 0.9484 passes at 39017; the stronger coefficient passes everywhere else in this range.')
    start = RULES[-1][0]
    for n in (start,start+1,start+1000):
        lower = bounds(n,True)[-1]
        # Strict upper bound: exhibit at least n primes <= integer x < n*lower/S.
        x = ceil_div(n*lower,S)-1
        count = quotient_count(x)
        assert count >= n, (n,x,count)
        print(f'Axler 10.667: n={n}, pi({x})={count} >= {n}.')


if __name__ == '__main__':
    main()
