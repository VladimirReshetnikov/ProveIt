"""Exact checks for phase gluing at coprime determinant and the top-shell threshold."""
from collections import Counter
from itertools import combinations_with_replacement
from math import gcd

from check_probes import (CyclotomicRing, canonical_rotation, divisors,
                          fixed_schedule, probe_values)


def determinant_mod_p(points, E, p):
    """Determinant of the integer convolution matrix, reduced mod p."""
    counts = Counter(points)
    rows = [[counts[(i-j) % E] % p for j in range(E)] for i in range(E)]
    det = 1
    for i in range(E):
        pivot = next((j for j in range(i,E) if rows[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            rows[pivot], rows[i] = rows[i], rows[pivot]
            det = -det
        det = det * rows[i][i] % p
        inv = pow(rows[i][i], -1, p)
        for j in range(i+1,E):
            scale = rows[j][i] * inv % p
            if scale:
                for k in range(i,E):
                    rows[j][k] = (rows[j][k] - scale * rows[i][k]) % p
    return det


def determinant_check(E, mass):
    ring = CyclotomicRing(E)
    pure = {label: row for label, row in fixed_schedule(E).items() if len(label) == 1}
    prime_divisors = [p for p in divisors(E)[1:] if len(divisors(p)) == 2]
    signatures = {}
    units = set()
    orbits = 0
    for x in combinations_with_replacement(range(E), mass):
        if x != canonical_rotation(E, x):
            continue
        orbits += 1
        signature = tuple(probe_values(ring, Counter(x), pure).values())
        signatures.setdefault(signature, []).append(x)
        nonzero = all(determinant_mod_p(x, E, p) for p in prime_divisors)
        if len(prime_divisors) == 1:
            assert nonzero == (mass % prime_divisors[0] != 0)
        if nonzero:
            units.add(signature)
    assert all(len(signatures[key]) == 1 for key in units)
    print(f"E={E:2} m={mass}: {orbits} rotation classes; "
          f"{len(units)} with determinant coprime to E, each alone in its pure-probe class")


def top_check(p, r):
    E = p**r
    ring = CyclotomicRing(E)
    row = fixed_schedule(E)[(E,)]
    def key(x):
        return ring.product(ring.fourier(Counter(x), k) for k in row)
    for m in range(1,p+1):
        by_value = {}
        for x in combinations_with_replacement(range(E),m):
            if x != canonical_rotation(E,x):
                continue
            assert by_value.setdefault(key(x),x) == x
    # Two order-p cosets have the same Fourier coefficient 0 at harmonic 1.
    # The common atoms at 0 make this coefficient nonzero for m>p.
    step = E//p
    for m in (p+1, p+2, 2*p, 3*p+1):
        x = (0,)*(m-p) + tuple(range(0,E,step))
        y = (0,)*(m-p) + tuple(range(1,E,step))
        assert canonical_rotation(E,x) != canonical_rotation(E,y)
        assert key(x) == key(y)
        assert ring.fourier(Counter(x),1) != ring.zero
    print(f"E={E:2}: top-shell signatures separate every orbit at each mass "
          f"1..{p}; four explicit masses above {p} have collisions")


def collision(E, x, y):
    ring = CyclotomicRing(E)
    pure = {label: row for label, row in fixed_schedule(E).items() if len(label) == 1}
    assert len(x)==len(y) and canonical_rotation(E,x) != canonical_rotation(E,y)
    assert probe_values(ring,Counter(x),pure) == probe_values(ring,Counter(y),pure)
    residues = {p: determinant_mod_p(x,E,p) for p in divisors(E)[1:]
                if len(divisors(p))==2}
    assert 0 in residues.values()
    print(f"E={E}, m={len(x)}, gcd(m,E)={gcd(len(x),E)}, determinant residues {residues}: "
          f"distinct multisets {x} and {y} have identical pure probes")


if __name__ == "__main__":
    print("Coprime determinant checks")
    for E,m in ((4,5),(8,3),(9,4),(6,5),(10,3),(12,5),(15,4)):
        determinant_check(E,m)
    print("Sharp top-shell threshold checks")
    for p,r in ((2,2),(2,3),(3,2),(3,3),(5,2)):
        top_check(p,r)
    print("Failures without determinant assumption")
    collision(4, (0,0,1,2), (0,0,2,3))
    collision(6, (0,0,0,1,2), (0,0,0,4,5))
