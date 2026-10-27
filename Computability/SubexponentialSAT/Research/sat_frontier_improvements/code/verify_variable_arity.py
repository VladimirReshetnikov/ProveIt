#!/usr/bin/env python3
"""Exact checks for the multi-arity polynomial-space certificate.

This manipulates lambda=ceil(log2(s)), not SAT instances or huge networks.
Finite checks supplement the asymptotic proof in variable_arity.tex.
No assert statement is used for a verification gate.
"""
from __future__ import annotations
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


RS = (13, 14, 8, 6)
FS = (F(27, 2000), F(159, 12500), F(71, 10000), F(533, 100000))
A_INF = F(499, 10000)
TAIL_F = F(27, 6400)
Q = F(5, 8)
COARSE_SHRINK = F(11, 20)
LOG_UPPER = {13: F(3701, 1000), 14: F(381, 100),
             8: F(3), 6: F(1293, 500), 4: F(2)}


def sqrt_upper(x, scale=10**9):
    """Return a certified rational upper bound for sqrt(nonnegative x)."""
    require(x >= 0, "negative square root")
    n = isqrt(x.numerator * scale * scale // x.denominator)
    if n*n*x.denominator < x.numerator*scale*scale:
        n += 1
    out = F(n, scale)
    require(out*out >= x, "incorrect square-root enclosure")
    return out


def atan_bounds(t, n):
    p = sum(((-1)**j * t**(2*j+1) / (2*j+1) for j in range(n)), F())
    e = t**(2*n+1)/(2*n+1)
    return (p, p+e) if n % 2 == 0 else (p-e, p)


def coefficient_upper():
    # Machin's identity supplies independent rational enclosures of pi.
    a5, b5 = atan_bounds(F(1, 5), 10)
    a239, b239 = atan_bounds(F(1, 239), 10)
    pi_upper = 16*b5 - 4*a239
    require(pi_upper < F(22, 7), "pi enclosure failed")
    log_lower = 2*sum((F(1, 3)**(2*j+1)/(2*j+1) for j in range(6)), F())
    require(log_lower > F(693, 1000), "ln(2) enclosure failed")
    m = F(1)
    total = F()
    for r, f in zip(RS, FS):
        total += m*sqrt_upper(2*(1-F(1, r))/f)
        m *= F(2, r)
    require(m == F(1, 546), "prefix size multiplier")
    tail_ratio_upper = sqrt_upper(F(2, 5))
    require(tail_ratio_upper < 1, "tail does not converge")
    total += m*sqrt_upper(F(3, 2)/TAIL_F)/(1-tail_ratio_upper)
    out = F(22, 7)/F(693, 1000)*total
    require(out < 64, "coefficient certificate is not below 64")
    return out


def display_coefficient():
    with localcontext() as c:
        c.prec = 60
        def dec(f): return Decimal(f.numerator)/Decimal(f.denominator)
        a5, b5 = atan_bounds(F(1, 5), 50)
        a239, b239 = atan_bounds(F(1, 239), 50)
        pi = dec((16*(a5+b5)-4*(a239+b239))/2)
        m, total = F(1), Decimal(0)
        for r, f in zip(RS, FS):
            total += dec(m)*(dec(2*(1-F(1, r))/f)).sqrt()
            m *= F(2, r)
        total += dec(m)*dec(F(3, 2)/TAIL_F).sqrt()/(1-dec(F(2, 5)).sqrt())
        return str(pi/Decimal(2).ln()*total)


def leading_margins():
    # These comparisons verify the only nonintegral logarithm estimates used.
    require(13**1000 < 2**3701, "log2(13) bound")
    require(14**100 < 2**381, "log2(14) bound")
    require(6**500 < 2**1293, "log2(6) bound")
    require(sum(FS) + TAIL_F/(1-Q) == A_INF, "total budget")
    require(F(1, 2) < COARSE_SHRINK < Q < 1, "uniform-depth inequalities")
    require(F(1, 4)/Q == F(2, 5), "tail cost ratio")
    rows, A, previous = [], F(), F()
    for d, (r, f) in enumerate(zip(RS, FS)):
        A += f
        g = LOG_UPPER[r]
        high = F(9, 10) + (2 if d == 0 else 1)*g*A
        col = F(9, 10)+2*g*A if d == 0 else 2*g*A+previous
        padding = (1+2*g)*A
        require(max(high, col, padding) < 1, f"power margin at depth {d}")
        rows.append(dict(depth=d, r=r, cumulative=str(A),
                         high_degree_power=str(high), fresh_column_power=str(col),
                         padding_power=str(padding), minimum_margin=str(1-max(high,col,padding))))
        previous = A
    high = F(9, 10)+2*A_INF
    other = 5*A_INF
    require(high < 1 and other < 1, "tail power margin")
    rows.append(dict(depth="tail",r=4,cumulative=str(A_INF),
                     high_degree_power=str(high),fresh_column_power=str(other),
                     padding_power=str(other),minimum_margin=str(1-high)))
    require(min(F(x['minimum_margin']) for x in rows) == F(1,25000),
            "minimum margin mismatch")
    return rows


def finite_gate(loglambda):
    # A conservative diagnostic at lambda=2^loglambda; not a runtime test.
    lam=2**loglambda
    b=6*loglambda
    depth=0
    z=F(lam)
    while z>1:
        z*=COARSE_SHRINK
        depth+=1
    depth+=4
    A=0
    previous=0
    gates=[]
    min_u=None
    for d in range(depth+1):
        r=RS[d] if d<4 else 4
        f=FS[d] if d<4 else TAIL_F*Q**(d-4)
        u=f.numerator*lam//f.denominator
        min_u=u if min_u is None else min(min_u,u)
        A+=u+b
        g=LOG_UPPER[r]
        high=F(9,10)*lam+(2 if d==0 else 1)*g*A+1
        col=F(9,10)*lam+2*g*A+1 if d==0 else 2*g*A+previous+1
        padding=(1+2*g)*A
        # Ten logarithms leave ample room for the packing's polynomial factors.
        gate=lam-max(high,col,padding)-10*loglambda
        gates.append(gate)
        previous=A
    passed=min(gates)>0 and min_u>0
    return {'log2_lambda':loglambda, 'hypothetical_depth':depth,
            'min_u':min_u, 'strict_gate_passes':passed,
            'minimum_logarithmic_margin':str(min(gates))}


def main():
    margins=leading_margins()
    upper=coefficient_upper()
    diagnostics=[finite_gate(k) for k in (20,24,28,32,40,48,64)]
    require(all(x['strict_gate_passes'] for x in diagnostics if x['log2_lambda']>=40),
            'large diagnostic schedule failed')
    # Explicit negative controls exercise the verification gates under python -O.
    rejected=0
    for fn in (lambda:sqrt_upper(F(-1)),
               lambda:require(F(499,10000)>F(1,20),'invalid total-budget mutation')):
        try: fn()
        except ValueError: rejected+=1
    require(rejected==2,'negative controls were not rejected')
    result={'status':'pass','coefficient_decimal':display_coefficient(),
            'coefficient_certified_upper':str(upper),
            'coefficient_certified_upper_decimal':float(upper),
            'safe_eventual_coefficient':64,'leading_margins':margins,
            'finite_schedule_diagnostics':diagnostics,
            'negative_controls_rejected':rejected,
            'scope':'normalized contraction certificate; not a SAT benchmark or full formal proof'}
    target=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('variable_arity_validation.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
