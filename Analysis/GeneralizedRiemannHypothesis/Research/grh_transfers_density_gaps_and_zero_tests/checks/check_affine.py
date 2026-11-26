"""Check candidate affine subgroups over explicit small square fields.

Build F_(p^f) with a primitive polynomial by a counted cycle over all
nonzero residues. Use field traces to enumerate the hyperplane, then
average each ordinary character row over the affine subgroup.
"""
from itertools import product
from math import isqrt


def primitive_field(p, f):
    q = p**f

    def digits(n):
        result = []
        for _ in range(f):
            n, digit = divmod(n, p)
            result.append(digit)
        return result

    def pack(coeffs):
        return sum(c*p**i for i, c in enumerate(coeffs))

    coords = list(map(digits, range(q)))

    def add(x, y):
        return pack([(a+b) % p for a,b in zip(coords[x], coords[y])])

    for poly in product(range(p), repeat=f):
        if poly[0] == 0:
            continue
        powers = []
        seen = set()
        x = 1
        while x not in seen and x != 0:
            seen.add(x)
            powers.append(x)
            high = coords[x][-1]
            shifted = [0] + coords[x][:-1]
            x = pack([(u-high*v) % p for u,v in zip(shifted, poly)])
        if x == 1 and len(powers) == q-1:
            return powers, add
    raise ArithmeticError("Primitive polynomial missing")


def verify(p, f, e):
    q, r = p**f, p**e
    assert f % (2*e) == 0
    powers, add = primitive_field(p, f)
    parity_sum = size_a = 0
    for i in range(q-1):
        trace = 0
        for j in range(f//e):
            trace = add(trace, powers[(i*r**j) % (q-1)])
        if trace == 0:
            size_a += 1
            parity_sum += (-1)**i
    size_a += 1  # zero in the hyperplane
    assert size_a == q//r
    size_c = r-1
    size_h = size_a*size_c
    torus = (q-1)//2
    assert torus % size_c == 0
    root = isqrt(q)
    assert root**2 == q

    def torus_sum(label):
        """Sum a split-torus character on the nonidentity scalars in C."""
        return size_c-1 if label % size_c == 0 else -1

    # Row sums on the identity, nonzero translations, and remaining cosets.
    char_sums = [size_h, q+size_a*(size_c-1)]
    for i in range(1, torus//2):
        char_sums.append(q+1 + size_a-1 + 2*size_a*torus_sum(i))
    char_sums.extend([q-size_a]*((q-1)//4))
    exceptional = []
    for sign in (1, -1):
        twice = q+1 + size_a-1 + sign*root*parity_sum
        assert twice % 2 == 0
        exceptional.append(twice//2 + size_a*torus_sum(torus//2))
    char_sums.extend(exceptional)
    assert len(char_sums) == (q+5)//2
    assert all(m >= 0 and m % size_h == 0 for m in char_sums)
    rich = all(char_sums)
    assert rich == ((q-1) % (4*(r-1)) == 0)
    pair = sorted(m//size_h for m in exceptional)
    print(f"q={q:3d} r={r:2d} |H|={size_h:3d} exceptional fixed dimensions {pair} rich={rich}")


if __name__ == "__main__":
    for example in [(3,2,1), (5,2,1), (7,2,1), (3,4,1), (3,4,2),
                    (11,2,1), (13,2,1), (5,4,1), (5,4,2)]:
        verify(*example)
