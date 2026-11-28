#!/usr/bin/env python3
"""Certify the finite cases of the quadratic derivative theorem with FLINT balls.

Requires python-flint 0.9.0. Run with python verify_derivatives.py > signs.csv.
The last field records signs of D_(m+1)-D_m from m=0 up to the analytic cutoff.
A positive sign is strict. The remaining differences follow from the paper.
"""
import csv
from functools import lru_cache
from math import factorial, gcd
import sys

from flint import acb_series, arb, ctx, dirichlet_char

CONDUCTOR_LIMIT = 384

@lru_cache(None)
def analytic_term(m, parity):
    """Part of the uniform lower bound independent of q."""
    ctx.prec, ctx.cap = 160, 2
    s = arb(4*m + 5)/2
    z = acb_series([s, 1]).zeta()
    return ((s + parity)/2).digamma()/2 + (z[1]/z[0]).real

def lower_bound(q, m, parity):
    ctx.prec = 160
    return analytic_term(m, parity) + (arb(q)/arb.pi()).log()/2

def cutoff(q, parity):
    m = 0
    while not lower_bound(q, m, parity) > 2:
        m += 1
    return m

def certify_prefix(q, chi, last):
    # FLINT series coefficients are Taylor coefficients, hence the factorials.
    for precision in (256, 512, 1024, 2048, 4096):
        ctx.prec, ctx.cap = precision, 2*last + 1
        s = acb_series([arb(1)/2, 1])
        a = chi.parity()
        completion = ((s+a) * ((arb(q)/arb.pi()).log()/2)).exp()
        completion *= ((s+a)/2).gamma() * s.dirichlet_l(chi)
        values = [(completion[2*m]*factorial(2*m)).real for m in range(last+1)]
        differences = [v-u for u, v in zip(values, values[1:])]
        if values[0] > 0 and all(v>0 or v<0 for v in differences):
            return ''.join('+' if v>0 else '-' for v in differences)
    raise ArithmeticError(f"Unresolved interval for modulus {q}, label {chi.number()}")

def main():
    assert lower_bound(CONDUCTOR_LIMIT, 0, 0) > 2
    rows, turning = [], []
    for q in range(3, CONDUCTOR_LIMIT):
        for label in range(1, q):
            if gcd(q,label) != 1:
                continue
            chi = dirichlet_char(q,label)
            if chi.order() != 2 or not chi.is_primitive():
                continue
            discriminant = (-1)**chi.parity() * q
            first_proved = cutoff(q, chi.parity())
            signs = certify_prefix(q, chi, first_proved)
            assert '+-' not in signs, (discriminant,signs)
            decreases = signs.count('-')
            if decreases:
                turning.append((discriminant,decreases))
            rows.append((discriminant, label, first_proved, decreases, signs))
    assert max(abs(d) for d,m in turning) == 97
    out = csv.writer(sys.stdout, lineterminator='\n')
    out.writerow(('D','Conrey_label','analytic_from_m','initial_decreases','finite_signs'))
    out.writerows(rows)
    print(f"{len(rows)} characters; {sum(r[2] for r in rows)} rigorous differences; "
          f"{len(turning)} strict minima.",file=sys.stderr)
    print(turning,file=sys.stderr)

if __name__ == '__main__':
    main()
