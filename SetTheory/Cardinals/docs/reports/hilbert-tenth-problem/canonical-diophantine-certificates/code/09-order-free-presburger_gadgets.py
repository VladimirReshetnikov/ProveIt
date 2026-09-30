#!/usr/bin/env python3
"""Unique natural witnesses for unbounded Presburger atoms.

Each penalty is quadratic and nonnegative whenever witness coordinates
are nonnegative reals. The affine operands x,y,L may be signed integers.
This is a gadget library, not a complete Presburger quantifier eliminator.
"""
from __future__ import annotations


def comparison_witness(x: int, y: int) -> tuple[int, int, int, int, int]:
    """Return (p,r,c,bar,h), with c == (x < y)."""
    if type(x) is not int or type(y) is not int:
        raise TypeError('Operands must be integers')
    p, r = max(y-x, 0), max(x-y, 0)
    c = int(p > 0)
    return p, r, c, 1-c, p-c


def comparison_penalty(x: int, y: int, w: tuple[int, ...]) -> int:
    if len(w) != 5:
        raise ValueError('A comparison witness has five coordinates')
    p, r, c, bar, h = w
    return ((x+p-y-r)**2 + p*r + (c+bar-1)**2
            + (p-c-h)**2 + bar*p)


def divisibility_witness(L: int, modulus: int) -> tuple[int, ...]:
    """Return (u,v,remainder,slack,p,r,c,bar,h); bar says modulus | L."""
    if type(modulus) is not int or modulus <= 0:
        raise ValueError('Modulus must be a positive integer')
    if type(L) is not int:
        raise TypeError('Operand must be an integer')
    q, remainder = divmod(L, modulus)
    return ((max(q, 0), max(-q, 0), remainder, modulus-1-remainder)
            + comparison_witness(0, remainder))


def divisibility_penalty(L: int, modulus: int, w: tuple[int, ...]) -> int:
    if modulus <= 0 or len(w) != 9:
        raise ValueError('Positive modulus and nine-coordinate witness required')
    u, v, remainder, slack = w[:4]
    return ((L-modulus*(u-v)-remainder)**2
            + (remainder+slack-(modulus-1))**2 + u*v
            + comparison_penalty(0, remainder, w[4:]))
