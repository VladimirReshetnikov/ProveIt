"""Independent orbit and game counts against the formulas in actions.tex."""
from itertools import product
from math import gcd


def mobius(n):
    count = 0
    p = 2
    while p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            count += 1
        p += 1
    return (-1)**count


def test_orbits():
    for q in range(4):
        for n in range(1, 8):
            necklaces, primitive, bracelets = set(), set(), set()
            for w in product(range(q), repeat=n):
                rots = {w[i:]+w[:i] for i in range(n)}
                necklace = min(rots)
                necklaces.add(necklace)
                if len(rots) == n:
                    primitive.add(necklace)
                bracelets.add(min(necklace, min(x[::-1] for x in rots)))
            divs = [d for d in range(1, n+1) if n % d == 0]
            r = sum(sum(gcd(a,d) == 1 for a in range(d))*q**(n//d) for d in divs)
            p = sum(mobius(d)*q**(n//d) for d in divs)
            refl = n*q**((n+1)//2) if n % 2 else (n//2)*(q**(n//2)+q**(n//2+1))
            assert r == n*len(necklaces)
            assert p == n*len(primitive)
            assert r + refl == 2*n*len(bracelets)


def mex(s):
    return next(x for x in range(len(s)+1) if x not in s)


def test_games():
    # Graphs of all lower-triangular move tables on four vertices.
    games = []
    for masks in product(*(range(1 << i) for i in range(4))):
        moves = [[j for j in range(i) if masks[i] >> j & 1] for i in range(4)]
        g = []
        for options in moves:
            g.append(mex({g[j] for j in options}))
        games.append((moves, g))
    for left, a in games:
        for right, b in games:
            joint = {}
            for i,j in product(range(4), repeat=2):
                options = {joint[x,j] for x in left[i]} | {joint[i,y] for y in right[j]}
                joint[i,j] = mex(options)
                assert joint[i,j] == a[i] ^ b[j]


if __name__ == "__main__":
    test_orbits()
    test_games()
    print("PASS: necklaces, primitive necklaces, bracelets, and XOR for 4,096 pairs of ranked games")
