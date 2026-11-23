"""Certified rounded errors for three approximations, with exact rational bounds."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
from certify_li import log_interval, ei_at, down, up

BASE = 1 << 150
K = 256


def zeta_values():
    result = []
    for j in range(1,K+1):
        n = 68 * (1 << ((14+j-1)//j))
        lo = sum(BASE // k**(j+1) for k in range(1,n+1))
        # Integral comparison on [n,infinity) and n outward rounding errors.
        tail = Q(1,j*n**j)
        result.append((Q(lo,BASE), Q(lo+n,BASE)+tail))
    return result


def gram(log_lo, log_hi, zeta):
    term_lo, term_hi = Q(1), Q(1)
    sum_lo, sum_hi = Q(1), Q(1)
    for j, (zl, zu) in enumerate(zeta, 1):
        term_lo = down(term_lo*log_lo/j)
        term_hi = up(term_hi*log_hi/j)
        sum_lo += down(term_lo/(j*zu))
        sum_hi += up(term_hi/(j*zl))
    return sum_lo, sum_hi+2*Q(34**(K+1),factorial(K+1))


def rounded(lo, hi):
    a = (lo+Q(1,2)).__floor__()
    assert a-Q(1,2) < lo <= hi < a+Q(1,2)
    return a


def main():
    counts = (Path(__file__).resolve().parents[1]/"verification"/"prime_table.txt").read_text().splitlines()[1:]
    expected = [
        (0,2,1), (3,5,1), (23,10,0), (143,17,-2), (906,38,-5),
        (6116,130,29),(44158,339,88),(332774,754,97),
        (2592592,1701,-79),(20758029,3104,-1828),(169923159,11588,-2318),
        (1416705193,38263,-1476),(11992858452,108971,-5773),
        (102838308636,314890,-19200)]
    assert len(counts) == len(expected)
    zetas = zeta_values()
    print("e  pi(10^e)  rounded(pi-x/log x)  rounded(li-pi)  rounded(R-pi)")
    for row, want in zip(counts,expected):
        exp,p,*_ = row.split()
        n,p=10**int(exp),int(p)
        lo, hi = log_interval(n)
        rl, rh = gram(lo,hi,zetas)
        got = (rounded(p-n/lo,p-n/hi), rounded(ei_at(lo)[0]-p,ei_at(hi)[1]-p),
               rounded(rl-p,rh-p))
        assert got == want, (n, got, want)
        print(exp,p,*got)

if __name__ == "__main__":
    main()
