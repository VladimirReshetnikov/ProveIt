"""Independent exact checks of product and bit rounding on auxiliary Pell tuples.
This is not a complete padded native witness and does not test source soundness.
No upstream code is imported or executed. Use explicit checks, valid under python -O.
"""
from math import gcd


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def pell_pair(base, exponent):
    D = base * base - 1
    x, y = 1, 0
    a, b = base, 1
    while exponent:
        if exponent & 1:
            x, y = x * a + D * y * b, x * b + y * a
        exponent >>= 1
        if exponent:
            a, b = a * a + D * b * b, 2 * a * b
    return x, y


def exact_div(a, b, label):
    q, r = divmod(a, b)
    require(r == 0, label)
    return q


def main():
    A, p = 3, 3
    Delta = A * A - 1
    _, c = pell_pair(A, p)
    M = p * c // gcd(c, Delta)
    require((c, M) == (35, 105), 'auxiliary constants')
    total = 0
    rows = []
    for ell in (1, 2, 3):
        m = M * ell
        f, z = pell_pair(A, m)
        R = Delta * z
        i = exact_div(R, c * c, 'i integrality')
        prior_bits = 0
        for n in (p, 4 * m - p, 4 * m + p):
            chi, y = pell_pair(R, n)
            U = exact_div(chi, R, 'U integrality')
            j = exact_div(U + p, c, 'j integrality')
            o = exact_div(U + c, f, 'o integrality')
            values = (f, i, j, o, y)
            require(all(x > 0 for x in values), 'positivity')
            product = f * i * j * o * y
            rhs = exact_div(R * y * (U + p) * (U + c), c ** 3, 'product quotient')
            require(product == rhs, 'product identity')
            bits = sum(x.bit_length() for x in values)
            require(0 <= bits - product.bit_length() <= 4, 'five-coordinate integer rounding')
            require(bits > prior_bits, 'sampled row bit monotonicity')
            prior_bits = bits
            require(R * R == Delta * (f * f - 1), 'first varying norm')
            require((R * U) ** 2 - (R * R - 1) * y * y == 1, 'second varying norm')
            total += 1
            rows.append((m, n, bits, bits - product.bit_length()))
    # Directly include ties at powers of two for the bit-rounding fact itself.
    for values in ((1, 1, 1, 1, 1), (2, 4, 8, 16, 32), (3, 7, 15, 31, 63)):
        product = 1
        for x in values:
            product *= x
        bits = sum(x.bit_length() for x in values)
        require(0 <= bits - product.bit_length() <= 4, 'rounding boundary')
    print(f'PASS: {total} exact auxiliary tuples; 3 direct rounding-boundary fixtures')
    print('m,n,varying_total_bits,total_minus_product_bits')
    for row in rows:
        print(','.join(map(str, row)))


if __name__ == '__main__':
    main()
