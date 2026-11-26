"""Verify the entries (membership) of Aiken et al., arXiv:2605.26020, Table A.7.

Run with Python 3.9+; the output CSV is written beside this script. All
calculations use integers. This finite check does not address other discriminants.
"""
import csv
from math import gcd, isqrt
from pathlib import Path

ABS_DISCRIMINANTS = (
    71, 151, 223, 251, 284, 343, 463, 467, 487, 587, 604, 811, 827, 859,
    892, 1163, 1171, 1372, 1483, 1523, 1627, 1787, 1852, 1948, 1987, 2011,
    2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107,
    5923, 63499, 118843,
)


def reduced_forms(discriminant):
    """One representative per proper class: |b|<=a<=c, b>=0 on ties."""
    for a in range(1, isqrt(abs(discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            c, rem = divmod(b * b - discriminant, 4 * a)
            if not rem and a <= c and gcd(a, b, c) == 1:
                if b >= 0 or (abs(b) != a and a != c):
                    yield (a, b, c)


def reduce_form(a, b, discriminant):
    """SL(2,Z) translations and coordinate interchange, then boundary convention."""
    while True:
        b = (b + a - 1) % (2 * a) - a + 1
        c, rem = divmod(b * b - discriminant, 4 * a)
        assert not rem
        if a <= c:
            return (a, abs(b) if a == c else b, c)
        a, b = c, -b


def bezout(a, b):
    """Return g,s,t with sa+tb=g=gcd(a,b)>=0."""
    r, s, t = a, 1, 0
    r2, s2, t2 = b, 0, 1
    while r2:
        q, rem = divmod(r, r2)
        r, r2, s, s2, t, t2 = r2, rem, s2, s - q * s2, t2, t - q * t2
    return (r, s, t) if r >= 0 else (-r, -s, -t)


def class_power(form, power, discriminant):
    """Build the ideal power as a rank-two Z-lattice, recover its norm form."""
    a, b, c = form
    e = discriminant % 2
    q = (e * e - discriminant) // 4  # w^2 = e*w-q
    k = (b - e) // 2
    # I=<a,k+w>. Its power has generators a^(power-j)*(k+w)^j.
    generators = []
    x, y = 1, 0
    for j in range(power + 1):
        scale = a ** (power - j)
        generators.append((scale * x, scale * y))
        x, y = k * x - q * y, x + (k + e) * y

    # Divide by the scalar content. The y-projection now has image Z:
    # closure under multiplication by w makes any common y-divisor
    # before normalization divide all x-coordinates as well.
    content = gcd(*(coordinate for pair in generators for coordinate in pair))
    gens = [(x // content, y // content) for x, y in generators]
    # The gcd of the two by two minors gives the index A of the lattice.
    minors = [x * v - y * u for i, (x, y) in enumerate(gens) for u, v in gens[:i]]
    big_a = gcd(*minors)
    assert big_a * content**2 == a**power
    # Find one lattice vector (r,1). Its class has basis (A,0),(r,1).
    bottom, top = 0, 0
    for x, y in gens:
        g, s, t = bezout(bottom, y)
        bottom, top = g, s * top + t * x
    assert bottom == 1
    r = top % big_a
    return reduce_form(big_a, 2 * r + e, discriminant)


def squarefree(n):
    return all(n % (k * k) for k in range(2, isqrt(n) + 1))


def fundamental_part(d):
    for f in range(1, isqrt(-d) + 1):
        if d % (f * f):
            continue
        d0 = d // (f * f)
        if d0 % 4 == 1 and squarefree(-d0):
            return d0, f
        if d0 % 4 == 0 and d0 // 4 % 4 in (2, 3) and squarefree(-d0 // 4):
            return d0, f
    raise ValueError(d)


def run():
    rows = []
    for abs_d in ABS_DISCRIMINANTS:
        d = -abs_d
        d0, conductor = fundamental_part(d)
        forms = list(reduced_forms(d))
        identity = forms[0]
        assert identity[0] == 1
        assert all(class_power(f, 1, d) == f for f in forms)
        assert all(class_power(f, 7, d) == identity for f in forms)
        assert len(forms) == (49 if abs_d in (63499, 118843) else 7)
        # For rank two give independent generators alongside the all-classes check.
        first = forms[1]
        cyclic = {identity} | {class_power(first, j, d) for j in range(1, 7)}
        assert len(cyclic) == 7
        second = next((f for f in forms if f not in cyclic), None)
        assert (second is not None) == (len(forms) == 49)
        rows.append((d, d0, conductor, len(forms), 7, 2 if second else 1,
                     " ".join(map(str, first)),
                     " ".join(map(str, second)) if second else ""))
    assert len(rows) == 40 and len(set(ABS_DISCRIMINANTS)) == 40
    assert sum(row[2] > 1 for row in rows) == 7
    path = Path(__file__).resolve().parent.parent / "class_groups.csv"
    with path.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("order_discriminant", "field_discriminant", "conductor",
                         "class_number", "exponent", "rank", "generator_1_abc",
                         "generator_2_abc"))
        writer.writerows(rows)
    print(f"Verified {len(rows)} order discriminants, 33 maximal and 7 nonmaximal.")
    print("38 groups C7, two groups C7 x C7; every class was raised to power 7.")


if __name__ == "__main__":
    run()
