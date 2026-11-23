"""Integer interval certificates for the finite inequalities in the paper."""
from bisect import bisect_right
from fractions import Fraction as Q
from math import isqrt
from certify_li import unit_log, log_interval

BOUND = 1_000_000
SCALE = 1 << 52
GRID = 1024


def sieve(n):
    flags = bytearray([1]) * (n+1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(n)+1):
        if flags[p]:
            flags[p*p::p] = bytes(1 + (n-p*p)//p)
    return flags


def log_cell(x):
    lo, hi = unit_log(x)
    return (int(lo*SCALE), (hi*SCALE).__ceil__())


# Positive dyadic units and the residual log(1+z), z - z²/2 <= log(1+z) <= z.
cells = [log_cell(Q(j, GRID)) for j in range(GRID, 2*GRID+1)]


def integer_log(n):
    a = n.bit_length()-1
    j, rem = divmod(n*GRID, 1 << a)
    den = j*(1 << a)
    low, high = cells[j-GRID]
    l2, h2 = cells[-1]
    return (a*l2 + low + SCALE*(2*rem*den-rem*rem)//(2*den*den),
            a*h2 + high + (SCALE*rem+den-1)//den)


def harmonic_examples(flags):
    H, count = Q(0), 0
    errors, initial = [], []
    for n in range(1, 1429):
        H += Q(1,n)
        count += flags[n]
        if n == 2:
            continue
        d = count - n/(H-Q(3,2))
        if d > 0:
            initial.append(n)
        if 50 <= n <= 1000:
            errors.append((d,n))
    assert initial[:7] == [1,109,113,114,199,200,201]
    low, argmin = min(errors)
    high, argmax = max(errors)
    assert argmin == 222 and argmax == 887
    assert Q(-2530,1000)<low<Q(-2529,1000) and Q(2779,1000)<high<Q(2780,1000)
    print("Harmonic approximation on [50,1000]: minimum at 222, maximum at 887.")
    print("Exact signed error lies between -2.530 and 2.780; first seven positive indices verified.")


def count_bounds(flags):
    lo113, hi113 = integer_log(113)
    h_low = count = theta_lower = 0
    max_upper = 125506
    for n in range(1,BOUND+1):
        count += flags[n]
        h_low += SCALE//n
        if n >= 1429:
            assert count*(2*h_low-3*SCALE) > 2*n*SCALE
        if n < 2:
            continue
        low, high = integer_log(n)
        if flags[n]:
            theta_lower += low
        assert 100000*count*high < max_upper*n*SCALE
        if n != 113:
            assert 113*count*high < 30*n*lo113
        if n >= 17:
            assert count*low > n*SCALE
        if n >= 5393:
            assert count*(low-SCALE) > n*SCALE
        if n >= 60184:
            assert count*(10*high-11*SCALE) < 10*n*SCALE
        # Cross-multiplied inequalities for the displayed Dusart polynomials.
        if n == 88783:
            small, large = Q(low,SCALE), Q(high,SCALE)
            def three_terms(v):
                return n*(1/v+1/v**2+2/v**3)
            assert Q(859604,100) < three_terms(large) <= three_terms(small) < Q(859605,100)
        if 88783 <= n <= 88788:
            assert count == 8596
            assert count*high**3 < n*SCALE*(low**2+low*SCALE+2*SCALE**2)
        if n >= 88789:
            assert count*low**3 >= n*SCALE*(high**2+high*SCALE+2*SCALE**2)
        assert 100*count*high**4 <= n*SCALE*(100*low**3+100*low**2*SCALE+
                                              200*low*SCALE**2+759*SCALE**3)
    assert count == 78498
    assert 100*theta_lower > 99*BOUND*SCALE
    assert 100*integer_log(BOUND)[1] < 1382*SCALE
    assert 4*30*lo113 > 5*113*SCALE
    print("theta(1000000) > 990000, log(1000000) < 13.82, and 30 log(113)/113 > 1.25.")
    print("Integer inputs through 1000000: Rosser-Schoenfeld pair, unique maximum at 113,")
    print("two Dusart denominator bounds and polynomial bounds; six counterexamples at 88783 through 88788 and passes from 88789.")
    print("Harmonic lower estimate strictly below pi(n) for every 1429 <= n <= 1000000.")


def ramanujan_samples(flags):
    # 2718281/10^6 < e < 2718282/10^6 by 12 Taylor terms.
    from math import factorial
    e0 = sum(Q(1,factorial(j)) for j in range(13))
    e1 = e0+Q(2,factorial(13))
    primes = [n for n in range(2,30) if flags[n]]
    good = []
    for n in range(2,19):
        i = (n/e1).__floor__()
        assert i == (n/e0).__floor__()
        p = bisect_right(primes,n)
        q = bisect_right(primes,i)
        lo, hi = log_interval(n)
        if p*p*hi < n*e0*q:
            good.append(n)
        else:
            assert p*p*lo > n*e1*q
    assert good == [6,9,10,12,14,15,16,18]
    print("First successes of Ramanujan's prime inequality through 18:", good)


if __name__ == "__main__":
    flags = sieve(BOUND)
    harmonic_examples(flags)
    ramanujan_samples(flags)
    count_bounds(flags)
