"""Independent exact checks of the rotating cutoff, field schedule and signs."""
from math import lcm, prod
from itertools import product
from bisect import bisect_right


def valuation(n, p):
    assert p >= 2 and n >= 1
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


def code(j):
    return tuple(valuation(j + 1, p) for p in (2, 3, 5, 7))


def grid(count):
    root = 10
    for j in range(count):
        yield root * root
        root += (j + 1).bit_length()


def main():
    samples = list(grid(96))
    for j, n in enumerate(samples):
        assert n == (10 + sum(i.bit_length() for i in range(1, j+1)))**2
    for target in product(range(4), repeat=4):
        m = prod(p**e for p, e in zip((2, 3, 5, 7), target))
        for h in range(5):
            assert code(m*(1 + 210*h)-1) == target
    print("Checked 96 grid values and 1,280 prescribed field returns.")
    selected = samples[:10]
    limits = sorted(set(selected) | {2*n for n in selected})
    current = 1
    log_lcm = {}
    for n in range(1, limits[-1]+1):
        current = lcm(current, n)
        if n in limits:
            log_lcm[n] = current.bit_length()-1
    for j,n in enumerate(selected):
        print(f"j={j:2d} n={n:4d} code={code(j)} ordinary gap={log_lcm[2*n]-2*log_lcm[n]:+4d}")
    # Both nontrivial sign cases and equality at exactly the budget.
    for a,b,k in product(range(11),range(11),range(17)):
        top = max(a-b,0)**2
        bottom = max(b-a,0)**2
        excess = max((a-b)**2-k,0)
        assert (top<=k) == ((excess if a>b else 0)==0)
        assert (bottom<=k) == ((excess if a<=b else 0)==0)
        assert (excess==0) == (top<=k and bottom<=k)
    print("Checked 2,057 signed comparisons with variable budgets.")
    # For each gap, its exact 2qh+h² expression is preserved.
    for x in range(100, samples[-1]):
        j = bisect_right(samples,x)-1
        h=(j+1).bit_length()
        assert x-samples[j] < 2*(10+sum(i.bit_length() for i in range(1,j+1)))*h+h*h


if __name__ == "__main__":
    main()
