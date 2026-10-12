"""Exact differential-polynomial research for the Gamma continuation.

Polynomials are sparse dictionaries: exponent tuples -> fractions.
This file supplies independent direct normal reduction and Euler homotopy.
"""
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
import json


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return tuple(a)


def add(*ps):
    out = {}
    for p in ps:
        for a, c in p.items():
            out[a] = out.get(a, F(0)) + c
    return {a: c for a, c in out.items() if c}


def scale(p, c):
    return {a: c*v for a, v in p.items() if c*v}


def varmul(p, j):
    out = {}
    for a, c in p.items():
        b = list(a) + [0]*max(0, j+1-len(a))
        b[j] += 1
        out[tuple(b)] = c
    return out


def deriv(p):
    out = {}
    for a, c in p.items():
        for j, e in enumerate(a):
            if e:
                b = list(a) + [0]
                b[j] -= 1
                b[j+1] += 1
                b = trim(b)
                out[b] = out.get(b, F(0)) + c*e
    return {a: c for a, c in out.items() if c}


def partial(p, j):
    out = {}
    for a, c in p.items():
        if len(a) > j and a[j]:
            b = list(a)
            e = b[j]
            b[j] -= 1
            out[trim(b)] = c*e
    return out


def raw_polynomials(max_weight):
    ps = [{(): F(1)}]
    for m in range(max_weight):
        ps.append(add(varmul(ps[-1], 0), scale(deriv(ps[-1]), -1)))
    return ps


@lru_cache(None)
def reduce_monomial(a):
    if len(a) < 2 or a[-1] >= 2:
        return {a: F(1)}, {}
    j = len(a)-1
    b = list(a)
    b[j] -= 1
    b[j-1] += 1
    b = trim(b)
    divisor = b[j-1]
    primitive = {b: F(1, divisor)}
    rest = add({a: F(1)}, scale(deriv(primitive), -1))
    n, h = normal_reduce(rest)
    return n, add(primitive, h)


def normal_reduce(p):
    nn, hh = {}, {}
    for a, c in p.items():
        n, h = reduce_monomial(a)
        nn = add(nn, scale(n, c))
        hh = add(hh, scale(h, c))
    return nn, hh


def euler(p):
    out = {}
    order = max(map(len, p), default=0)
    for j in range(order):
        term = partial(p, j)
        for _ in range(j):
            term = deriv(term)
        out = add(out, scale(term, (-1)**j))
    return out


def boundary_operator(p):
    out = {}
    order = max(map(len, p), default=0)
    for j in range(1, order):
        term = partial(p, j)
        for k in range(j):
            out = add(out, scale(varmul(term, j-1-k), (-1)**k))
            term = deriv(term)
    return out


def homotopy(p):
    """Closed homotopy: B K^{-1}; no recursive integration by parts."""
    assert not p.get((), 0)
    return boundary_operator({a: c/F(sum(a)) for a, c in p.items()})


def partitions_weight(weight, last=None):
    if weight == 0:
        yield ()
        return
    if last is None:
        last = weight
    if last == 1:
        yield (weight,)
        return
    for e in range(weight//last+1):
        for a in partitions_weight(weight-last*e, last-1):
            yield trim(a + (0,)*(last-1-len(a)) + (e,))


def polyprod(a, b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def cp(r):
    return [F(1, 2**r*factorial(j)*factorial(r+1-j))
            if (j-r) % 2 == 0 else F(0) for j in range(r+1)]


def universal_coefficient(a):
    m = sum((i+1)*e for i, e in enumerate(a))
    if len(a) <= 1:
        return F(1)
    d = len(a)-1
    if a[-1] < 2 or sum(i*e for i, e in enumerate(a)) % 2:
        return F(0)
    p = [F(1)]
    for r in range(1, d+1):
        for _ in range(a[r] - (2 if r == d else 0)):
            p = polyprod(p, cp(r))
    integral = F(0)
    for e, c in enumerate(p):
        den = 1
        for j in range(d+1):
            den *= e+1+2*j
        integral += c/F(den)
    prefactor = F((-1)**d*factorial(m), 2**d*factorial(d+1))
    for e in a:
        prefactor /= factorial(e)
    return prefactor*integral


def universal_normal(m):
    out = {}
    for a in partitions_weight(m):
        c = universal_coefficient(a)
        if c:
            out[a] = c
    return out


def serialize(p):
    return [{"exponents": list(a), "coefficient": str(c)}
            for a, c in sorted(p.items())]


def tex_poly(p):
    out = []
    for a, c in sorted(p.items(), reverse=True):
        coeff = str(abs(c))
        if c.denominator != 1:
            coeff = r"\frac{%d}{%d}" % (abs(c.numerator), c.denominator)
        mon = "".join("u_{%d}" % i + ("^{%d}" % e if e != 1 else "")
                      for i, e in enumerate(a) if e)
        if mon and abs(c) == 1:
            coeff = ""
        out.append(("-" if c < 0 else "+") + coeff + mon)
    return " ".join(out).lstrip("+") or "0"


def main(max_weight=20):
    ps = raw_polynomials(max_weight)
    checks = []
    data = []
    for m, a in enumerate(ps):
        n, recursive_h = normal_reduce(a)
        direct_n = universal_normal(m)
        assert n == direct_n, (m, "universal normal coefficients")
        p = add(a, scale(direct_n, -1))
        h = homotopy(p)
        assert h == recursive_h, (m, "homotopy against recursive primitive")
        assert add(direct_n, deriv(h)) == a, (m, "exact derivative")
        assert not euler(p), (m, "Euler exactness")
        kp = {aa: F(sum(aa))*c for aa, c in p.items()}
        assert add(varmul(euler(p), 0), deriv(boundary_operator(p))) == kp
        checks.append({"weight": m, "raw_terms": len(a), "normal_terms": len(n),
                       "primitive_terms": len(h), "checks": 5})
        data.append({"weight": m, "normal": serialize(n), "primitive": serialize(h)})
        print(m, len(a), len(n), len(h), flush=True)
        if m in [4, 5, 6, 8]:
            print("N_"+str(m), tex_poly(n))
            print("H_"+str(m), tex_poly(h))
    # A corruption must be detected by the defining derivative identity.
    h = normal_reduce(ps[8])[1]
    corrupt = add(h, {(5, 1): F(1)})
    assert add(universal_normal(8), deriv(corrupt)) != ps[8]
    out = {"max_weight": max_weight, "exact_assertions": 5*len(ps)+1,
           "corruption_rejected": True, "weights": checks, "data": data}
    from pathlib import Path
    dest = Path(__file__).parent
    (dest/'normal_forms_results.json').write_text(json.dumps(out, indent=2)+"\n")
    print("PASS", out['exact_assertions'], "exact assertions")


if __name__ == '__main__':
    main()
