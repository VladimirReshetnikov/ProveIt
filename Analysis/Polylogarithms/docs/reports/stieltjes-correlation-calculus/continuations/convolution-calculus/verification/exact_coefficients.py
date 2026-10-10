"""Exact formal coefficients for the Stieltjes convolution theorems.

No floating-point arithmetic or integer-relation search is used.  The symbols
Zk denote zeta(k), Ak denote gamma_k(a), and Bk denote gamma_k(1-a).
The finite truncation checks the printed examples and universal algebra, not
the analytic finite-part theorem; that theorem is proved in the article.
"""
import json
from pathlib import Path
import sympy as S

u, v = S.symbols('u v')
DEGREE = 6
Z = {k: S.Symbol(f'Z{k}') for k in range(2, DEGREE + 1)}
A = {k: S.Symbol(f'A{k}') for k in range(DEGREE)}
B = {k: S.Symbol(f'B{k}') for k in range(DEGREE)}


def truncate(expr, degree=DEGREE):
    poly = S.Poly(S.expand(expr), u, v)
    return S.Add(*(c*u**i*v**j for (i, j), c in poly.terms()
                   if i+j <= degree))


def exp_truncated(expr):
    result = S.Integer(1)
    power = S.Integer(1)
    for k in range(1, DEGREE // 2 + 1):
        power = truncate(power*expr)
        result += power / S.factorial(k)
    return S.expand(result)


def coeff(expr, i, j):
    return S.expand(expr).coeff(u, i).coeff(v, j)


def swapped(expr):
    return expr.xreplace({u: v, v: u})


def kernels():
    w = u+v
    log_e = sum(Z[k]*(u**k+v**k-w**k)/k for k in Z)
    log_f = sum(Z[k]*(u**k+(-1)**k*(w**k-v**k))/k for k in Z)
    e = exp_truncated(log_e)
    f = exp_truncated(log_f)
    g = swapped(f)
    quotient, remainder = S.div(S.Poly(v*f+u*g, u, v), S.Poly(w, u, v))
    assert remainder.is_zero
    q = quotient.as_expr()
    ha = sum((-1)**k*A[k]*w**k/S.factorial(k) for k in A)
    hb = sum((-1)**k*B[k]*w**k/S.factorial(k) for k in B)
    reflected = truncate(-e*(1+w*ha))
    circular = truncate(-q-v*f*ha-u*g*hb)
    return e, reflected, circular


def value(expr, n, m):
    return S.expand((-1)**(n+m)*S.factorial(n)*S.factorial(m)
                    * coeff(expr, n+1, m+1))


def main():
    e, reflected, circular = kernels()
    checks = 0
    # Boundary cancellation, symmetry, and leading-index coefficients.
    assert S.expand(reflected-swapped(reflected)) == 0
    assert S.expand(circular-swapped(circular).xreplace(
        {**{A[k]: B[k] for k in A}, **{B[k]: A[k] for k in B}})) == 0
    checks += 2
    rows = []
    for n in range(5):
        for m in range(5-n):
            r, c = value(reflected, n, m), value(circular, n, m)
            high = n+m+1
            assert r.coeff(A[high]) == S.Rational(n+m+2, (n+1)*(m+1))
            assert c.coeff(A[high]) == S.Rational(1, n+1)
            assert c.coeff(B[high]) == S.Rational(1, m+1)
            checks += 3
            rows.append(dict(n=n, m=m, reflected=str(r), circular=str(c)))
    expected = {
        (0, 0): 2*A[1]+Z[2],
        (1, 0): S.Rational(3, 2)*A[2]-Z[2]*A[0]-Z[3],
        (1, 1): A[3]-2*Z[2]*A[1]+2*Z[3]*A[0]
                +S.Rational(3, 2)*Z[4]-Z[2]**2/2,
        (2, 0): S.Rational(4, 3)*A[3]-2*Z[2]*A[1]+2*Z[3]*A[0]+2*Z[4],
    }
    for nm, rhs in expected.items():
        assert S.expand(value(reflected, *nm)-rhs) == 0
        checks += 1
    assert value(circular, 0, 0) == A[1]+B[1]-2*Z[2]
    assert S.expand(value(circular, 1, 0) - (
        A[2]/2+B[2]+Z[2]*(A[0]+B[0])-Z[3])) == 0
    checks += 2
    # Independently check the one-digamma formula for every available n.
    for n in range(5):
        rhs = S.Rational(n+2, n+1)*A[n+1] + (-1)**n*S.factorial(n)*Z[n+2]
        rhs += sum((-1)**j*S.factorial(n)/S.factorial(n-j)*Z[j+1]*A[n-j]
                   for j in range(1, n+1))
        assert S.expand(value(reflected, n, 0)-rhs) == 0
        checks += 1
    # Bell-polynomial identities from an independent univariate expansion.
    t, X = S.symbols('t X')
    bell_exp = S.exp(-X*t+sum(Z[k]*t**k/k for k in Z)).series(t, 0, 7).removeO()
    qn = {n: S.expand((-1)**(n+1)*S.factorial(n)*bell_exp.coeff(t, n+1))
          for n in range(5)}
    assert S.expand(X**2-2*qn[1]+Z[2]) == 0
    assert S.expand(X**3-3*qn[2]+3*Z[2]*X-2*Z[3]) == 0
    checks += 2
    output = dict(degree=DEGREE, exact_assertions=checks, identities=rows,
                  convolution_polynomials={str(n): str(p) for n, p in qn.items()})
    path = Path(__file__).with_name('exact_coefficients.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    print(f'{checks} exact assertions passed; {len(rows)} pairs generated.')
    for row in rows:
        if row['n'] >= row['m'] and row['n']+row['m'] <= 3:
            print(row)


if __name__ == '__main__':
    main()
