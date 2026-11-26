"""Independent 65-digit cross-check of the rigorous rational explicit-formula certificate.

Uses the overlap lengths of shifted step intervals to calculate the test at
each prime power, trial division for primes, and explicit lists of blocks.
The independently enclosed rational proof is in checks/explicit_bound.py.
"""
from decimal import Decimal as D, getcontext
from functools import cache
from math import gcd, isqrt

getcontext().prec = 65
FLOOR = 31 * 10**19
OLD = [21, 14, 10, 6, 4, 1]
NEW = [1000, 933, 686, 449, 251, 81]


def check(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def primes(y):
    return [p for p in range(2, y + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


@cache
def data(y, half):
    heights = half + tuple(-a for a in reversed(half))
    norm = sum(a*a for a in heights)
    n = len(heights)
    width = D(y).ln() / n
    # Direct overlaps: the correlation at t is a weighted sum of triangular
    # functions centred at the distance j-i between each pair of intervals.
    def overlap(t):
        return sum(a*b*max(D(0), 1-abs(t-(j-i)))
                   for i,a in enumerate(heights)
                   for j,b in enumerate(heights)) / norm
    knots = [overlap(D(i)) for i in range(n + 1)]
    lip = max(abs(b-a)/width for a,b in zip(knots,knots[1:]))
    inert_sum = D(0)
    charge = {}
    for p in primes(y):
        lp = D(p).ln()
        zi, zs = D(0), D(0)
        pk, k = p, 1
        while pk <= y:
            value = D(0) if pk == y else overlap(D(pk).ln()/width)
            term = 2*lp*value/D(pk).sqrt()
            zi += (-1)**k * term
            zs += term
            pk *= p
            k += 1
        inert_sum += zi
        charge[p] = max(D(0), zi - zs)
    return inert_sum + 2 - D(14)*lip/9, charge


def count_row(low, high, y, half, mult):
    baseline, loss = data(y, tuple(half))
    blocks = []
    if mult:
        bmax = isqrt((4*max(loss)**7)//low)
        visited = set()
        for b in range(1,bmax+1):
            if b not in visited:
                block = [i for i in range(b,bmax+1,b) if i//b<=mult and i not in visited]
                visited.update(block)
                blocks.append(block)
        check(visited == set(range(1,bmax+1)), "block partition")
        for block in blocks:
            for a in block:
                for b in block:
                    check(max(a,b)//gcd(a,b)<=mult, "ratio safety")
        check((mult<=12 and y<=4200) or (mult==1 and y<=6500), "scope of sieve")
    else:
        check(low == 4*y**7, "inert-only window")
    total = sum(max([D(0)] + [l for p,l in loss.items() if 4*p**7 >= low*min(block)**2])
                for block in blocks)
    margin = baseline - total - D(high).ln()
    check(margin>0, "nonpositive margin")
    print(f"{low} {high} {y} {mult} {len(blocks)} {baseline:.8f} {total:.8f} {margin:.8f}")
    return margin


def main():
    upper = 39 * 10**29
    rows = []
    for y in [7000,5000,4700,4600]:
        lower=4*y**7
        rows.append((lower,upper,y,OLD,0))
        upper=lower
    for lower,y in [(4*10**22,6500),(10**22,4900)]:
        rows.append((lower,upper,y,OLD,1))
        upper=lower
    lower=FLOOR
    for a,b in [(105,100),(115,100),(130,100),(150,100),(180,100),(2,1),(3,1),(4,1)]:
        if lower>=upper:
            break
        high=min(upper,lower*a//b)
        rows.append((lower,high,4200,NEW,12))
        lower=high
    intervals=sorted((l,u) for l,u,*_ in rows)
    check(intervals[0][0]==FLOOR and intervals[-1][1]==39*10**29, "exterior endpoints")
    check(all(b==c for (_,b),(c,_) in zip(intervals,intervals[1:])), "gap")
    print("lower upper Y multiplier blocks baseline charge margin")
    margins = [count_row(*row) for row in rows]
    print(f"{len(rows)} rows; smallest excess above log(upper): {min(margins):.8f}")


if __name__=="__main__":
    main()
