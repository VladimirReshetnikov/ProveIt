#!/usr/bin/env python3
"""Exact sparse polynomial utilities extracted from the inherited parent audit.

This code uses only Python's standard library. It does not execute imported
repository code and never decides solvability. Source JSON data are read as
data. The inherited full-B2 command-line driver is deliberately omitted.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


def add(a, b, sign=1):
    r = dict(a)
    for m, c in b.items():
        r[m] = r.get(m, 0) + sign * c
        if not r[m]:
            del r[m]
    return r


def mul(a, b):
    r = {}
    for m, c in a.items():
        for n, d in b.items():
            k = tuple(x + y for x, y in zip(m, n))
            r[k] = r.get(k, 0) + c * d
    return {m: c for m, c in r.items() if c}


def shift_positive(poly, variable_count):
    """Apply every witness x_i -> x_i+1; leave four ports unchanged."""
    result = {}
    for monomial, coefficient in poly.items():
        choices = [range(e + 1) for e in monomial[:variable_count]]
        for witness_monomial in itertools.product(*choices):
            c = coefficient
            for before, after in zip(monomial, witness_monomial):
                c *= math.comb(before, after)
            m = tuple(witness_monomial) + monomial[variable_count:]
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}

