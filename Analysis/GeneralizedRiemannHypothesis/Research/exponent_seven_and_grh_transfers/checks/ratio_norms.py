"""Rule out split primes with norm coefficients in ratios i:j, 1<=i<j<=12.

The local filters discard pairs only when a necessary local norm condition
fails. The GNU coreutils 9.7 proof-enabled build of factor proves primality. All subsequent arithmetic
uses exact Python integers. NumPy accelerates only finite Boolean set operations.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import islice
from math import gcd
import numpy as np
from equal_norms import FLOOR, divisors, factor_batch, primes_to

LIMIT = 4200
MAX_MULTIPLIER = 12
MODULI = [(2,7),(3,4),(5,3),(7,2),(11,2),(13,1),(17,1),(19,1),(23,1)]
PRIMES = [p for p in primes_to(LIMIT) if 4*p**7 > FLOOR]
WITNESSES = [(r,{j*j % r for j in range(1,r)}) for r in primes_to(700)
             if r > MAX_MULTIPLIER and 4*r**7 < FLOOR]


def local_masks(base, exponent, multiplier):
    mod = base**exponent
    squares = {c*c % mod for c in range(mod)}
    unit = 3 if base == 2 else next(k for k in range(1,base)
                                    if pow(-k,(base-1)//2,base) == base-1)
    # x*c^2 lies in this set, including when the common factor c is nonunit.
    possible = sorted({unit*t % mod for t in squares})
    assert len(possible) <= 64
    def mask(p):
        value = 4*pow(p,7,mod)
        return sum(1 << k for k,t in enumerate(possible)
                   if (value-multiplier*multiplier*t) % mod in squares)
    masks = [mask(r) for r in range(mod)]
    return np.array([masks[p % mod] for p in PRIMES],dtype=np.uint64)


def jobs():
    tables = {i:[local_masks(r,k,i) for r,k in MODULI]
              for i in range(1,MAX_MULTIPLIER+1)}
    allowed = {i:np.array([4*p**7>FLOOR*i*i for p in PRIMES])
               for i in tables}
    distinct = ~np.eye(len(PRIMES),dtype=bool)
    for j in range(2,MAX_MULTIPLIER+1):
        for i in range(1,j):
            if gcd(i,j)!=1:
                continue
            eligible = distinct & allowed[i][:,None] & allowed[j][None,:]
            for a,b in zip(tables[i],tables[j]):
                eligible &= (a[:,None] & b[None,:]) != 0
            rows,cols = np.nonzero(eligible)
            pairs = ((PRIMES[a],PRIMES[b]) for a,b in zip(rows,cols))
            while chunk := list(islice(pairs,500)):
                yield i,j,chunk


def check(job):
    i,j,pairs = job
    ds = [i*i*q**7-j*j*p**7 for p,q in pairs]
    counts = [len(pairs),0,0]
    for (p,q),signed,fac in zip(pairs,ds,factor_batch([abs(d) for d in ds])):
        d = abs(signed)
        assert d
        for u in divisors(fac):
            if u*u>d:
                continue
            v = d//u
            # If i*a_q is the larger coordinate, j*a_p = v-u.
            ja = v-u if signed>0 else v+u
            if ja % j:
                continue
            a = ja//j
            m = 4*p**7-a*a
            if m<=FLOOR*i*i or m%(i*i):
                continue
            m //= i*i  # candidate x*c^2
            iq = v+u if signed>0 else v-u
            if iq%i or 4*q**7-(iq//i)**2!=j*j*m:
                continue
            counts[1] += 1
            for r,residues in WITNESSES:
                if (-m)%r in residues:
                    counts[2] = max(counts[2],r)
                    break
            else:
                raise ArithmeticError((i,j,p,q,u,m))
    return i,j,counts


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--workers',type=int,default=4)
    args=parser.parse_args()
    totals = {}
    with ProcessPoolExecutor(args.workers) as pool:
        for i,j,counts in pool.map(check,jobs(),chunksize=1):
            row=totals.setdefault((i,j),[0,0,0])
            row[0]+=counts[0]; row[1]+=counts[1]; row[2]=max(row[2],counts[2])
    for (i,j),row in sorted(totals.items()):
        print(i,j,*row)
    print('ordered pairs after local tests',sum(v[0] for v in totals.values()))
    print('divisor candidates',sum(v[1] for v in totals.values()))
    print('largest first witness',max(v[2] for v in totals.values()))
    print('survivors 0')


if __name__=='__main__':
    main()
