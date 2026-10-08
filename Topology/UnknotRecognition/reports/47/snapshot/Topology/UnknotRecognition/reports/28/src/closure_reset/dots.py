"""R_p = F2[x_0,...,x_(p-1)]/(x_i^2), packed by squarefree monomials.
Bit S of an integer is the coefficient of product(x_i : i in S).
"""
from __future__ import annotations

def monomials(f: int):
    if type(f) is not int or f < 0: raise ValueError('invalid polynomial')
    while f:
        low = f & -f
        yield low.bit_length() - 1
        f ^= low

def validate(f: int, p: int, *, radical=False):
    if type(p) is not int or p < 0 or type(f) is not int or f < 0:
        raise ValueError('invalid dot polynomial')
    if f.bit_length() > (1 << p): raise ValueError('too many dot variables')
    if radical and (f & 1): raise ValueError('constant term is forbidden')

def parity(f: int) -> int:
    """Sum of singleton-monomial coefficients, not total coefficient parity."""
    return sum(1 for s in monomials(f) if s and s & (s - 1) == 0) & 1

def multiply(f: int, g: int) -> int:
    out = 0
    for s in monomials(f):
        for t in monomials(g):
            if not s & t: out ^= 1 << (s | t)
    return out

def derivative(f: int) -> int:
    out = 0
    for s in monomials(f):
        t = s
        while t:
            low = t & -t
            out ^= 1 << (s ^ low)
            t ^= low
    return out

def quotient(f: int, owners: list[int] | tuple[int, ...]) -> int:
    """Substitute x_i -> y_owners[i]; repeated variables kill a monomial."""
    out = 0
    for s in monomials(f):
        target = 0
        while s:
            low = s & -s
            bit = 1 << owners[low.bit_length() - 1]
            if target & bit: break
            target |= bit
            s ^= low
        else:
            out ^= 1 << target
    return out
