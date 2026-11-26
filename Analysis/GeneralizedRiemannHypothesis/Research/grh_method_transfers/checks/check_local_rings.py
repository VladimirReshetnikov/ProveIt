"""Exact small-ring checks. Run with Python 3.9+ and assertions enabled."""
from itertools import product
from fractions import Fraction
from random import Random


class Ring:
    """Z/p^2, or F_p plus a square-zero F_p-vector space."""
    def __init__(self, p, rank, mixed=False):
        self.p, self.rank = p, rank
        self.size = p ** (rank + 1)
        assert not mixed or rank == 1
        self.name = f"Z/{p*p}" if mixed else f"F_{p} + (F_{p})^{rank}"
        def ops(a, b):
            if mixed:
                return (a+b) % self.size, (a*b) % self.size
            a0, b0 = a % p, b % p
            s, v = (a0+b0) % p, a0*b0 % p
            for i in range(1, rank+1):
                place = p**i
                ai, bi = (a//place) % p, (b//place) % p
                s += ((ai+bi) % p)*place
                v += ((a0*bi+b0*ai) % p)*place
            return s, v
        table = [[ops(a,b) for b in range(self.size)] for a in range(self.size)]
        self.add = [[s for s,v in row] for row in table]
        self.mul = [[v for s,v in row] for row in table]

    def product(self, f, g):
        if not f or not g:
            return ()
        out = [0]*(len(f)+len(g)-1)
        for i,a in enumerate(f):
            if a:
                for j,b in enumerate(g):
                    out[i+j] = self.add[out[i+j]][self.mul[a][b]]
        return trim(out)

    def residue_degree(self, f):
        return max((i for i,a in enumerate(f) if a % self.p), default=-1)

    def deleted(self, f, n):
        if self.p == 2:
            return len(f) <= n-1
        return len(f) <= n and self.residue_degree(f) <= n-2


def trim(f):
    out = list(f)
    while out and not out[-1]:
        out.pop()
    return tuple(out)


def verify_packing(ring, n=3):
    q, Q = ring.p, ring.size
    seen = set()
    for f in product(range(Q), repeat=n):  # top coefficient at n is zero
        if q == 2:
            if f[-1] or not f[-2]:
                continue
            r = (0,1)
        else:
            if f[-1] % q or not f[-2] % q or not f[0] % q:
                continue
            # Compute c in the annihilator directly from the ring table.
            candidates = [c for c in range(0,Q,q) if ring.add[f[-1]][
                ring.mul[ring.add[c][c]][f[-2]]] == 0]
            assert len(candidates) == 1
            c, = candidates
            r = trim((c,1,c))
        f = trim(f)
        y = ring.product(f,r)
        z = ring.product(y,r)
        assert max(len(f),len(y),len(z)) <= n+1
        assert len({f,y,z}) == 3 and seen.isdisjoint((f,y,z))
        seen.update((f,y,z))
    w = Fraction(1,Q*Q if q == 2 else Q*q)
    gamma = 1-Fraction(1,Q) if q == 2 else (1-Fraction(1,q))**2
    assert Fraction(len(seen),Q**(n+1)) == 3*w*gamma
    return len(seen)//3


def check_triple(ring, f, r, a, b, n):
    y = f
    for _ in range(a):
        y = ring.product(y,r)
    z = y
    for _ in range(b):
        z = ring.product(z,r)
    if len(y)>n+1 or len(z)>n+1:
        return 0
    assert ring.deleted(f,n) or ring.deleted(y,n) or ring.deleted(z,n)
    return 1


def verify_deletions(ring):
    # Every ratio of actual degree <=2 and every start in B_2
    # whose residue degree permits a three-term ordinary progression.
    n, Q, p = 2, ring.size, ring.p
    polys = [trim(f) for f in product(range(Q),repeat=n+1)]
    starts = [f for f in polys if ring.residue_degree(f)==0]
    ratios = [r for r in polys if ring.residue_degree(r)==1]
    valid = sum(check_triple(ring,f,r,1,1,n) for f in starts for r in ratios)
    assert valid
    assert sum(ring.deleted(f,n) for f in polys) == Q**(n+1)//(
        Q*Q if p==2 else Q*p)
    # Larger unequal gaps and ratios with high nilpotent coefficients.
    random = Random(20261126)
    weighted = 0
    n = 7
    for a,b in ((1,2),(2,1),(2,2),(1,3),(3,1),(2,3)):
        for _ in range(250):
            f = [random.randrange(Q) for j in range(1+random.randrange(n-a-b+1))]
            f[0] = random.choice([v for v in range(Q) if v % p])
            f.extend(random.randrange(0,Q,p) for j in range(random.randrange(3)))
            r = trim((random.randrange(Q),1,random.randrange(0,Q,p)))
            weighted += check_triple(ring,trim(f),r,a,b,n)
    assert weighted
    return valid, weighted


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    for ring in [Ring(2,1,True),Ring(2,1),Ring(3,1,True),Ring(3,1),Ring(3,2)]:
        count = verify_packing(ring)
        if ring.size <= 9:
            ordinary, weighted = verify_deletions(ring)
            print(f"{ring.name}: {count} disjoint triples; "
                  f"{ordinary} ordinary and {weighted} unequal-gap instances checked.")
        else:
            print(f"{ring.name}: {count} disjoint triples.")
    print("All finite-ring checks passed.")
