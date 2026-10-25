"""Pure polynomial helpers from independent audit/check_signed_transform.py.
The parent workflow copied this exact function block for portable replay.
"""
from collections import defaultdict

def require(x, msg):
    if not x:
        raise ValueError(msg)

def plus(*parts):
    out = defaultdict(int)
    for p in parts:
        for m,c in p.items():
            out[m] += c
    return {m:c for m,c in out.items() if c}

def times(p,q):
    out = defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():
            out[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in out.items() if c}

def scaled(p,a):
    return {m:c*a for m,c in p.items() if c*a}

def v(name):
    return {(name,):1}

def row_named(row,names):
    out = defaultdict(int)
    for c,mon in row['terms']:
        out[tuple(sorted(names[i] for i in mon))] += c
    return {m:c for m,c in out.items() if c}

def fingerprint(row):
    return tuple(sorted(row.items()))

