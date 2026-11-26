"""Exact checks of the integer density separation for rational and integer ratios."""
from itertools import combinations
from math import isqrt, lcm, prod
from fractions import Fraction

def primes_through(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[0:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            for n in range(p*p, limit+1, p):
                prime[n] = 0
    return [p for p in range(2,limit+1) if prime[p]]

def finite_witness(integer_only):
    triples = [(a,b,c) for a,b,c in combinations(range(1,13),3)
               if b*b == a*c and (not integer_only or b%a == 0)]
    masks = [sum(1<<(a-1) for a in t) for t in triples]
    def free(u):
        return all(u & mask != mask for mask in masks)
    greedy = 0
    for k in range(12):
        candidate = greedy | 1<<k
        if free(candidate):
            greedy = candidate
    witness = sum(1<<(i-1) for i in (1,2,5,6,7,8,9,10,11,12))
    assert greedy.bit_count()==9 and free(witness) and witness.bit_count()==10
    valid = [i for i in range(1<<12) if free(i)]
    prefix = [(1<<k)-1 for k in range(1,13)]
    maxima = [max((u&m).bit_count() for u in valid) for m in prefix]
    assert not any(all((u&m).bit_count()==v for m,v in zip(prefix,maxima)) for u in valid)
    print('integer ratios' if integer_only else 'rational ratios', triples, maxima)

def bound():
    Y, K, scale = 2000, 100000, 10**18
    product_lower, tail_upper = scale, scale//K
    for p in primes_through(K):
        if p<=Y:
            product_lower = product_lower*(p-1)//p
        else:
            tail_upper += (scale+p*p-1)//(p*p)
    lower = product_lower//156-tail_upper
    assert lower*10**6 > 404*scale
    print('Certified common gap >=', lower, '/', scale)

def upper(primes, cutoff, kind):
    def generate(j,x):
        if j==len(primes):
            yield x
        else:
            while x<=cutoff:
                yield from generate(j+1,x)
                x*=primes[j]
    smooth=sorted(generate(0,1))
    assert len(set(smooth))==len(smooth)
    index={h:i for i,h in enumerate(smooth)}
    denom=lcm(*smooth)
    weights=[denom//h for h in smooth]
    links=[[] for _ in smooth]
    for i,a in enumerate(smooth):
        for j in range(i+1,len(smooth)):
            b=smooth[j]
            if kind=='integer' and b%a:
                continue
            c,r=divmod(b*b,a)
            if r==0 and c in index:
                links[j].append((1<<i,1<<index[c]))
    incumbent=0
    def dfs(selected, remaining, score, potential):
        nonlocal incumbent
        if potential<=incumbent:return
        if not remaining:
            incumbent=score
            return
        bit=remaining & -remaining
        i=bit.bit_length()-1
        rest=remaining ^ bit
        blocked=0
        for earlier,later in links[i]:
            if selected&earlier:blocked |= later
        blocked &= rest
        kept=rest^blocked
        potential_with=potential
        while blocked:
            x=blocked & -blocked
            potential_with-=weights[x.bit_length()-1]
            blocked^=x
        dfs(selected|bit,kept,score+weights[i],potential_with)
        dfs(selected,rest,score,potential-weights[i])
    dfs(0,(1<<len(smooth))-1,0,sum(weights))
    c=prod(Fraction(p-1,p) for p in primes)
    return 1-c*Fraction(sum(weights)-incumbent,denom),len(smooth),Fraction(incumbent,denom)

def integer_weight_bound():
    result, n, weight = upper((2,3,5,7),5000,'integer')
    assert (result,n,weight) == (Fraction(5245322990569,7001316000000),265,
                                Fraction(1619153731921,497871360000))
    gap = Fraction(818410,10**6) - result
    assert gap > Fraction(69218,10**6)
    print('Integer ratio, finite smooth mass:', weight, 'natural-density upper bound:', result)
    print('With McNew 4.4, integer-ratio gap >', gap)

if __name__=='__main__':
    finite_witness(False)
    finite_witness(True)
    bound()
    integer_weight_bound()
