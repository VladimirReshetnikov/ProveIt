"""Exact A399421 rows from equation (47), Agranat-Tamir et al.

Public mathematical source: https://arxiv.org/abs/2601.08062 .
The polynomial implementation was refactored from independent_rows.py in the
2 October 2026 computational investigation. It reads no precomputed triangle.

G = z + (G^2 + G(z^2,u^2))/2
      + zu/2 * ((G/(1-G))^2 + G(z^2,u^2)/(1-G(z^2,u^2))).
Introduce S=G/(1-G), so S=G+GS. All coefficients below are integers.
"""
import argparse
import json
from pathlib import Path


def addto(a, b, shift=0, factor=1):
    a.extend([0] * max(0, len(b) + shift - len(a)))
    for j, value in enumerate(b):
        a[j + shift] += factor * value


def convolution(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                result[i + j] += x * y
    return result


def square_coefficient(n, sequence):
    result = [0]
    # Symmetry avoids evaluating every product twice.
    for i in range(1, (n + 1) // 2):
        addto(result, convolution(sequence[i], sequence[n-i]), factor=2)
    if n > 0 and n % 2 == 0:
        addto(result, convolution(sequence[n//2], sequence[n//2]))
    return result


def generate_triangle(limit=160):
    if limit < 1:
        raise ValueError("The leaf limit must be positive")
    g = [[0] for _ in range(limit + 1)]
    s = [[0] for _ in range(limit + 1)]
    for n in range(1, limit + 1):
        a = square_coefficient(n, g)
        if n % 2 == 0:
            for j, value in enumerate(g[n//2]):
                addto(a, [value], 2*j)
        b = square_coefficient(n-1, s)
        if n % 2 == 1:
            for j, value in enumerate(s[(n-1)//2]):
                addto(b, [value], 2*j)
        addto(a, b, 1)
        assert all(value % 2 == 0 for value in a), (n, "nonintegral orbit count")
        g[n] = [value // 2 for value in a]
        if n == 1:
            g[n][0] += 1
        while len(g[n]) > 1 and g[n][-1] == 0:
            g[n].pop()
        s[n] = g[n].copy()
        for i in range(1, n):
            addto(s[n], convolution(g[i], s[n-i]))
    return g


def wedderburn_etherington(limit):
    """Independent univariate recurrence U=x+(U^2+U(x^2))/2."""
    u = [0] * (limit+1)
    if limit:
        u[1] = 1
    for n in range(2, limit+1):
        numerator = sum(u[j] * u[n-j] for j in range(1, n))
        if n % 2 == 0:
            numerator += u[n//2]
        assert numerator % 2 == 0
        u[n] = numerator // 2
    return u


def endpoint_coefficient(rows, n, d):
    """[w^n e^d]H; inadmissible parity/support is exactly zero."""
    if n < 1 or d < 0 or d > n-1 or (n-d) % 2 != 1:
        return 0
    k = (n-d-1)//2
    return rows[n][k] if k < len(rows[n]) else 0


def check_transformed_equation(rows, limit=16):
    """Check the full transformed rational equation with sparse exact algebra.

    This check uses polynomial multiplication and geometric expansions directly,
    rather than the S-recursion used for triangle generation. It checks every
    coefficient with w-degree <= limit, including zero/parity coefficients.
    """
    def add(*terms):
        out = {}
        for term in terms:
            for key, value in term.items():
                out[key] = out.get(key, 0) + value
        return {key: value for key, value in out.items() if value}

    def mul(a, b):
        out = {}
        for (n, d), x in a.items():
            for (m, e), y in b.items():
                if n+m <= limit:
                    key = (n+m, d+e)
                    out[key] = out.get(key, 0) + x*y
        return out

    def shift(a, n=0, d=0, factor=1):
        return {(i+n, j+d): factor*v for (i, j), v in a.items() if i+n <= limit}

    h = {(n, n-2*k-1): value for n in range(1, limit+1)
         for k, value in enumerate(rows[n]) if value}
    nested = {(2*n, 2*d): value for (n, d), value in h.items() if 2*n <= limit}
    hh = mul(h, h)
    first = {}
    power = hh
    # H^2/(1-eH)^2 = sum_{j>=0}(j+1)e^j H^(j+2).
    for j in range(limit):
        first = add(first, shift(power, d=j, factor=j+1))
        power = mul(power, h)
    second = {}
    power = nested
    for j in range(limit):
        second = add(second, shift(power, d=2*j))
        power = mul(power, nested)
    rhs = add({(1, 0): 2}, shift(add(hh, nested), d=1),
              shift(add(first, second), n=1))
    assert rhs == shift(h, factor=2), "Transformed equation residual is nonzero"
    return {"checked_through_w_degree": limit, "nonzero_residual_coefficients": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=160)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = generate_triangle(args.limit)
    result = {"max_n": args.limit, "indexing": "rows[n][k]=g[n,k]; row 0 is [0]",
              "rows": rows, "totals": [sum(row) for row in rows]}
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
