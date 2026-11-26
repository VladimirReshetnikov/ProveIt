"""Independent direct residue enumeration of every prime-power presieve mask.

Pass the directory containing ratio_norms.py. No matching of representatives,
Hensel lifting or bit operations are used to generate the expected sets.
"""
from collections import Counter, defaultdict
from math import gcd
from importlib import import_module
from math import isqrt
from pathlib import Path
import sys


def require(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: python review_masks.py /path/to/checks")
    sys.path.insert(0,str(Path(sys.argv[1]).resolve()))
    sieve=import_module('ratio_norms')
    primes=[i for i in range(2,4201) if all(i%d for d in range(2,isqrt(i)+1))
            and 4*i**7>31*10**19]
    require(primes==sieve.PRIMES, "prime table")
    tested=0
    direct = {}
    for r, k in sieve.MODULI:
        mod=r**k
        nonzero_squares={i*i%r for i in range(1,r)}
        if r==2:
            xvals={x for x in range(mod) if x%8==3}
        else:
            xvals={x for x in range(mod) if x%r and (-x)%r not in nonzero_squares}
        ms=sorted({x*c*c%mod for x in xvals for c in range(mod)})
        sqrtres=[a*a%mod for a in range(mod)]
        # Enumerate in the forward direction (a,M) -> allowed RHS 4p^7.
        for i in range(1,13):
            by_rhs={w:set() for w in range(mod)}
            for m in ms:
                for a2 in sqrtres:
                    by_rhs[(a2+i*i*m)%mod].add(m)
            direct[(r,i)] = [by_rhs[4*pow(p,7,mod)%mod] for p in primes]
            packed=sieve.local_masks(r,k,i)
            for p,mask in zip(primes,packed,strict=True):
                indexset={m for bit,m in enumerate(ms) if int(mask)//(1<<bit)%2}
                require(indexset==by_rhs[4*pow(p,7,mod)%mod],(r,k,i,p))
                tested+=1
        print(f"r={r} k={k} modulus={mod} discriminant classes={len(xvals)} M residues={len(ms)}")
    print(f"{tested} masks match direct enumeration over x, c, a")
    # Independently enumerate the acceptable q for each p. Each bit now indexes
    # a prime q, rather than a possible common norm residue. Union over residues
    # at one modulus, then intersect these sets of primes across moduli.
    prime_index = {p:k for k,p in enumerate(primes)}
    expected_rows = {}
    floor = 31*10**19
    for j in range(2,13):
        eligible = sum(1<<qidx for qidx,q in enumerate(primes) if 4*q**7>j*j*floor)
        columns = {}
        for r,k in sieve.MODULI:
            buckets = defaultdict(int)
            for qidx,residues in enumerate(direct[(r,j)]):
                for t in residues:
                    buckets[t] |= 1<<qidx
            columns[r] = buckets
        for i in range(1,j):
            if gcd(i,j)>1:
                continue
            rows = []
            for pidx,p in enumerate(primes):
                bits = eligible & ~(1<<pidx) if 4*p**7>i*i*floor else 0
                for r,k in sieve.MODULI:
                    keep = 0
                    for t in direct[(r,i)][pidx]:
                        keep |= columns[r][t]
                    bits &= keep
                    if not bits:
                        break
                rows.append(bits)
            expected_rows[i,j] = rows
    independent_count = sum(bits.bit_count() for rows in expected_rows.values() for bits in rows)
    pairs=Counter()
    for i,j,chunk in sieve.jobs():
        pairs[(i,j)]+=len(chunk)
        for p,q in chunk:
            row = expected_rows[i,j]
            ix, qbit = prime_index[p], 1<<prime_index[q]
            require(row[ix] & qbit, ("extra or duplicate pair",i,j,p,q))
            row[ix] ^= qbit
    require(not any(any(rows) for rows in expected_rows.values()), "missing pairs")
    require(sum(pairs.values())==independent_count, "pair count")
    print(f"{independent_count} locally possible ordered prime/ratio pairs; {len(pairs)} nonempty reduced-ratio types")
    print("Every ordered (i,j,p,q) agrees in independent and production enumerations.")


if __name__=='__main__':
    main()
