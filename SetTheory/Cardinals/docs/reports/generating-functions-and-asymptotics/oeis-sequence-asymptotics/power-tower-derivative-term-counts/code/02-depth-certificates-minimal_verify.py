#!/usr/bin/env python3
"""Standalone exact certificate from Appendix A of article.tex."""
def must(test):
    if not test:
        raise ArithmeticError("certificate failure")

def column(d, q, K):
    r = 2*d + 1 + q
    a = [1] + [0]*d
    for j in range(r):
        a = [(2*d-j)*a[i] + (a[i-1] if i else 0)
             for i in range(d+1)]
    out = [a[d]]
    if K == 0:
        return out
    b = [(2*d-q)*a[i] + (2*a[i-1] if i else 0)
         for i in range(d+1)]
    out.append(b[d])
    for k in range(1, K):
        c = [(2*d-q)*b[i] + (2*b[i-1] if i else 0)
             + k*(k+r)*a[i] for i in range(d+1)]
        out.append(c[d])
        a, b = b, c
    return out

for d, R, Q in [(3, 14, 38), (4, 85, 185)]:
    for q in range(Q):
        for k, value in enumerate(column(d, q, R-2)):
            hole = (q == 2*d and (k+d) % 2 == 0)
            must((value == 0) == hole)
            if not hole:
                must(value % 1009 != 0 or value % 1013 != 0)
    must(column(d, 2*d, R)[R] > 0)
    ks, ka = (d-1) % 2, d % 2
    must((-1)**Q * column(d, Q, ks)[ks] > 0)
    must((-1)**(Q+1) * column(d, Q, ka)[ka] > 0)
print("PASS")
