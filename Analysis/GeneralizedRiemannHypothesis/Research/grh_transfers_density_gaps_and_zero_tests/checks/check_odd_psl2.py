"""Exact, table-independent checks of the odd PSL(2,p) Gelfand weight.

Run with python3 check_odd_psl2.py. The group-algebra commutator identity
certifies all squared character coefficients. Positivity on the center
certifies their signs. Arithmetic throughout is integral.
"""
from collections import Counter
from itertools import product
from fractions import Fraction


def positive_definite(matrix):
    """Symmetric rational elimination with positive pivots (Sylvester)."""
    a = [[Fraction(x) for x in row] for row in matrix]
    assert all(a[i][j] == a[j][i] for i in range(len(a)) for j in range(i))
    for i in range(len(a)):
        pivot = a[i][i]
        assert pivot > 0
        for j in range(i + 1, len(a)):
            factor = a[j][i] / pivot
            for k in range(i + 1, len(a)):
                a[j][k] -= factor * a[i][k]


def verify(p):
    def canonical(a, b, c, d):
        mat = tuple(x % p for x in (a, b, c, d))
        return min(mat, tuple((-x) % p for x in mat))

    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return canonical(a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)

    def inv(x):
        a, b, c, d = x
        return canonical(d, -b, -c, a)

    def power(x, n):
        ans = identity
        while n:
            if n % 2:
                ans = mul(ans, x)
            x = mul(x, x)
            n //= 2
        return ans

    identity = canonical(1, 0, 0, 1)
    group = {canonical(a,b,c,d) for a,b,c,d in product(range(p), repeat=4)
             if (a*d-b*c) % p == 1}
    size = len(group)
    assert size == p * (p*p-1) // 2
    inverses = {x: inv(x) for x in group}
    class_id, classes, reps = {}, [], []
    for x in sorted(group):
        if x in class_id:
            continue
        orbit = {mul(mul(y, x), inverses[y]) for y in group}
        for y in orbit:
            class_id[y] = len(classes)
        classes.append(orbit)
        reps.append(x)
    first = p % 4 == 1
    dim = p*(p+1)//2 + int(first)

    def weight(x):
        if x == identity:
            return dim
        discriminant = ((x[0] + x[3])**2 - 4) % p
        if discriminant == 0:
            return int(first)
        split = pow(discriminant, (p-1)//2, p) == 1
        if split != first:
            return 1
        order = (p-1)//2 if split else (p+1)//2
        square = power(x, order//2) == identity
        return 2 * int(square == first)

    weights = {x: weight(x) for x in group}
    assert sum(weights.values()) == size
    gram = []
    for x, orbit in zip(reps, classes):
        assert all(weights[y] == weights[x] for y in orbit)
        assert all(weights[y] == weights[inverses[y]] for y in orbit)
        convolution = sum(weights[b]*weights[mul(inverses[b], x)] for b in group)
        commutators = sum(size//len(classes[class_id[b]]) for b in group
                          if class_id[mul(x, b)] == class_id[b])
        assert convolution == commutators
        gram.append([len(orbit) * sum(weights[mul(x, inverses[y])] for y in other)
                     for other in classes])
    positive_definite(gram)

    if first:
        # Split torus normalizer in its diagonal/antidiagonal matrix model.
        normalizer = {x for x in group if (x[1],x[2])==(0,0) or (x[0],x[3])==(0,0)}
        reflection = canonical(0, 1, -1, 0)
        sums = Counter()
        for x in normalizer:
            torus_element = x if (x[1],x[2])==(0,0) else mul(x,reflection)
            value = 1 if power(torus_element, (p-1)//4) == identity else -1
            sums[class_id[x]] += value
        for i, x in enumerate(reps):
            assert (weights[x]-1)*len(normalizer) == (size//len(classes[i]))*sums[i]

    print(f"p={p:2d}  |G|={size:4d}  classes={len(classes):2d}  "
          f"dimension={dim:3d}  PASS")


if __name__ == "__main__":
    for prime in (5, 7, 11, 13, 17, 19):
        verify(prime)
