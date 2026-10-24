"""Small exact sparse-polynomial operations; Python standard library only."""
import collections
import json

def add(a, b, sign=1):
    out = collections.defaultdict(int, a)
    for mon, coef in b.items():
        out[mon] += sign * coef
    return {mon: coef for mon, coef in out.items() if coef}

def mul(a, b):
    out = collections.defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return {mon: coef for mon, coef in out.items() if coef}

def enc(poly):
    return [[coef, list(mon)] for mon, coef in sorted(poly.items())]

def dump(path, obj):
    path.write_text(json.dumps(obj, separators=(",", ":")) + "\n")
