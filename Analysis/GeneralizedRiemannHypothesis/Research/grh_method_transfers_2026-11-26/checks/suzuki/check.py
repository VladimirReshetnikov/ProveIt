"""Verify finite resonance and moment bounds for Suzuki's unsmoothed sign race.

Dependencies: NumPy and python-flint. The input cells are [a,a+1]/10^22.
Regenerate the entire cell file with generate.py, or verify the reduction
from the supplied cells alone with this script. All comparisons used in
certification are integer comparisons or outward-rounded Arb comparisons.
"""
from pathlib import Path
import math
import numpy as np
from flint import arb, ctx

ctx.prec = 120
SCALE = 10**22
COARSE = 10**14
blocks = [(500, 6000), (6000, 12000), (12000, 18000)]

def verify_pairs(cells):
    # A coarser floor supports vectorized sorted differences. Each true
    # ordinate in these units is in [u,u+1], since 10^14 divides 10^22.
    u = np.array([a // (SCALE // COARSE) for a in cells], dtype=np.int64)
    assert 2 * int(u[-1]) + 3 < np.iinfo(np.int64).max
    n = len(u)
    # When all ordinates are within a factor of three there is no 3-vs-1
    # relation. Otherwise also compare all positive sums against differences.
    three_to_one = 3 * int(u[0]) <= int(u[-1]) + 1
    N = n*n if three_to_one else n*(n-1)//2
    buf = np.empty(N, dtype=np.int64)
    pos = 0
    for i in range(n):
        buf[pos:pos+i] = u[i] - u[:i]
        pos += i
        if three_to_one:
            buf[pos:pos+i+1] = u[i] + u[:i+1]
            pos += i+1
    assert pos == N
    buf.sort()
    # A difference's error lies in [-1,1], a sum's in [0,2].
    # Gaps strictly above 3 separate every pair of enclosures.
    gap = min(int(np.diff(buf[max(0,start-1):start+1000000]).min())
              for start in range(0,N,1000000))
    assert gap > 3
    return N, gap

def sqrt(x): return x.sqrt()

def run():
    cells = [int(s) for s in Path(__file__).with_name('zero_cells.txt').read_text().splitlines()]
    assert len(cells) == blocks[-1][1] and all(a+1 < b for a,b in zip(cells,cells[1:]))
    ys = [(arb(n)+arb('0.5 +/- 0.5')) / SCALE for n in cells]
    vs = []
    for i,j in [(0,500)] + blocks:
        vs.append(sum(2/y**2 for y in ys[i:j]))
        if i:
            N,g = verify_pairs(cells[i:j]); print(f'indices {i+1}..{j}: entries={N}, smallest gap={g} * 10^-14')
        print(f'variance {i+1}..{j}: {vs[-1].str(14)}')
    # Brent-Platt-Trudgian (2022), eq. (20), Cor. 1 and Lemmas 5-6.
    H = arb(3*10**12); L=H.log(); pi=arb.pi()
    extra = arb('0.56')*(L**2+((2*pi).log()-1)*L)/(2*pi*H)
    total_upper=2*(arb('0.023105')+extra)
    tail=total_upper-sum(vs)
    print('tail variance upper bound',tail.str(12))
    c=(pi/2+(8*pi).log()+arb.const_euler())/2
    a,b=arb('0.79'),arb('0.37')
    r=9
    low = sqrt(math.prod(range(1,2*r,2))*vs[0]**r/2)*(r-1)**(r-1)/(r**r*a**(r-1))
    mid = sqrt(arb(3)/2)*sum(sqrt(v) for v in vs[1:])**2/(4*b)
    high=sqrt(tail/2)
    bound=((low+mid+high)/(c-a-b))**2
    print('c =', c.str(12), 'r =',r,'a =',a.str(4),'b =',b.str(4))
    print('low excess norm bound',low.str(12),'middle excess norm bound',mid.str(12),'high positive-part norm bound',high.str(12))
    print('rare-sign upper bound',bound.str(14))
    assert bound < arb('0.00007943')
    # A positive weighted mean gives a constructive lower bound for the rare sign.
    T = arb(1420)
    assert ys[999] < T and ys[1000] > T
    weights = [2 * (1/y - 1/T) for y in ys[:1000]]
    first = sum(weights[:500]); second = sum(weights[500:])
    k = 23
    delta = first * k / (k+1) - second - c
    max_weight = (arb(4)**k / math.comb(2*k,k))**500
    probability_lower = (delta/max_weight)**2 / total_upper
    assert delta > 0 and probability_lower > arb(10)**(-937)
    print('positive filter first sum',first.str(12),'remaining sum',second.str(12))
    print('positive filter margin',delta.str(12),'rare-sign lower bound',probability_lower.str(12))

if __name__ == '__main__': run()
