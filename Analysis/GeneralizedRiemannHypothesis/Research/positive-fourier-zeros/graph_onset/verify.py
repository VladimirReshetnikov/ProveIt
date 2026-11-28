"""Exact independent checks for the graph-tower onset paper. Python 3, standard library."""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import comb
from random import Random


def vp(n, p):
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def direct(terms, p, h):
    """Reduce the exponent polynomial modulo Phi, then expand in zeta - 1."""
    step = p ** (h - 1)
    e = (p - 1) * step
    a = [0] * (p * step)
    for exponent, coefficient in terms:
        a[exponent % (p * step)] += coefficient
    rem = [a[k] - a[e + k % step] for k in range(e)]
    best = None
    for j in range(e):
        vj = sum(comb(k, j) * rem[k] for k in range(j, e) if rem[k])
        if vj:
            v = vp(vj, p)
            # p/(zeta-1)^e reduces to -1 at the residue field.
            order = e * v + j
            lead = ((vj // p**v) * (-1)**v) % p
            if best is None or order < best[0]:
                best = (order, lead)
    return best


def tree(terms, p, h):
    """Recursive splitting, centering every node at its first exponent."""
    shift = terms[0][0]
    centered = [(n - shift, c) for n, c in terms]
    if h == 1:
        return direct(centered, p, h)
    children = defaultdict(list)
    for n, c in centered:
        q, r = divmod(n, p)
        children[r].append((q, c))
    result = {r: tree(t, p, h - 1) for r, t in children.items()}
    finite = [value[0] for value in result.values() if value is not None]
    if not finite:
        return None
    least = min(finite)
    for delta in range(p):
        unit = sum(value[1] * comb(r, delta) for r, value in result.items()
                   if value is not None and value[0] == least and r >= delta) % p
        if unit:
            return p * least + delta, unit
    raise AssertionError("Distinct occupied residues must be independent.")


def check_recursion():
    rng = Random(229819)
    results = Counter()
    for p, top in ((2,7),(3,4),(5,3),(7,3)):
        for h in range(1, top + 1):
            n = p ** h
            cases = [[(0,1), (n,-1)], [(0,p**4), (n // p, p**4)],
                     [(j * n // p, 1) for j in range(p)]]
            for _ in range(165):
                occupied = rng.randrange(1,10)
                shift = rng.randrange(-2*n, 2*n)
                scale = p ** rng.randrange(h+1)
                common = p ** rng.randrange(4)
                cases.append([(shift + scale*rng.randrange(-n,n+1),
                               common*rng.randrange(-10,11)) for _ in range(occupied)])
            for terms in cases:
                expected = direct(terms,p,h)
                actual = tree(terms,p,h)
                assert actual == expected, (terms, p, h, actual, expected)
                results[p] += 1
                results["zeros"] += expected is None
    return results


def dot(a, b):
    return sum(x*y for x,y in zip(a,b))


def det3(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def rank3(forms):
    if any(det3(*triple) for triple in combinations(forms,3)):
        return 3
    for a,b in combinations(forms,2):
        if any(a[i]*b[j] != a[j]*b[i] for i,j in combinations(range(3),2)):
            return 2
    return int(any(any(a) for a in forms))


def cell_counts(forms, p, h):
    frequencies = Counter()
    n = p**h
    lookup = [(h,0)] + [(vp(v,p), (v // p**vp(v,p)) % p) for v in range(1,n)]
    for x in product(range(n), repeat=3):
        key = tuple(lookup[dot(a,x) % n] for a in forms)
        frequencies[key] += 1
    return frequencies


def check_volumes():
    forms = ((2,2,0), (1,0,1), (1,2,-1), (1,0,0), (0,1,0), (0,0,1))
    p = 2
    bound = max(vp(det3(*a),p) for a in combinations(forms,3) if det3(*a))
    # This uses the sharp determinant bound from the gap proof.
    counts = {h: cell_counts(forms,p,h) for h in (4,5,6)}
    checks = Counter()
    for h in (4,5):
        for key, count in counts[h].items():
            levels = sorted({0,h-1,h} | {k for k,angular in key})
            for u,v in zip(levels,levels[1:]):
                if v == h or v-u <= bound:
                    continue
                deep = [a for a,(k,_) in zip(forms,key) if k >= v]
                r = rank3(deep)
                shifted = tuple((k+(k>=v), angular) for k,angular in key)
                assert counts[h+1][shifted] == count*p**(3-r)
                checks[r] += 1
    assert len(checks) == 4
    pole_cases = 0
    for h,cells in counts.items():
        for key in cells:
            levels = sorted({0,h-1,h} | {k for k,angular in key})
            gaps = [(u,v) for u,v in zip(levels,levels[1:]) if v < h and v-u > bound]
            ranks = [rank3([a for a,(k,_) in zip(forms,key) if k >= v]) for _,v in gaps]
            assert all(r > q for r,q in zip(ranks,ranks[1:]))
            test_marks = {k for k,angular in key[:3] if k < h-1} | {h-1}
            for digit in test_marks:
                factors = [3-r-int(digit < v) for r,(_,v) in zip(ranks,gaps)]
                multiplicities = Counter(factors)
                assert all(0 <= w <= 3 for w in factors)
                assert multiplicities[3] <= 1 and max(multiplicities.values(),default=0) <= 2
                assert sum(value == 2 for value in multiplicities.values()) <= 1
                pole_cases += 1
    return bound, checks, pole_cases


def examples():
    # Character sums on the full rank-three grid. All sums below are integer exact.
    rows = []
    for h in range(1,5):
        p, k = 2, 2
        n = p ** h
        e = n // 2
        accum = [0,0,0]
        for x,y,z in product(range(n), repeat=3):
            product_terms = [(4*i*x+j*y+l*z, (-1)**(3-i-j-l))
                             for i,j,l in product((0,1),repeat=3)]
            base = [(0,12)] + [(sgn*v,-2) for v in (x,y,z) for sgn in (-1,1)]
            moved = base + [(0,2), (4*x,-1), (-4*x,-1)]
            for slot, terms in enumerate((product_terms,base,moved)):
                data = direct(terms,p,h)
                if data:
                    accum[slot] += data[0]
        assert all(v % e == 0 for v in accum)
        torus, base, moved = (v // e for v in accum)
        theoretical = 0 if h <= k else (p**k*(h-k)*(n-1)**2
                                        + 2*h*(n-p**k)*(n-1))
        assert torus == theoretical
        rows.append((h,torus,base-3*h,moved-3*h))
    return rows


if __name__ == "__main__":
    res = check_recursion()
    print("Direct reduction versus recursive order and leading residue")
    for p in (2,3,5,7):
        print(f"p={p}, {res[p]} comparisons")
    print(f"Zero evaluations among these: {res['zeros']}")
    b, checks, pole_cases = check_volumes()
    print(f"Rank-three cell comparisons. Maximum determinant valuation {b}.")
    for r, n in sorted(checks.items()):
        print(f"Deep rank {r}: {n} exact cell-size identities")
    print(f"Cell and digit-position denominator patterns checked: {pole_cases}")
    print("h | Laurent-product total | base graph valuation | perturbed graph valuation")
    for row in examples():
        print(*row, sep=" | ")
    print("All checks passed.")
