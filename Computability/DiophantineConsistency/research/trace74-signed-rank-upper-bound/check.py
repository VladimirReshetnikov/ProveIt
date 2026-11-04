#!/usr/bin/env python3
"""Check the guard-free signed-rank upper-bound identity over Z."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("run with python3 -I -S -B")

root = Path(__file__).resolve().parents[2]
source = root / "research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean"
expected = "83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0"
content = source.read_bytes()
assert hashlib.sha256(content).hexdigest() == expected
text = content.decode()
for line in (
    "let bJ := beta * J", "let q := bJ + 1", "let q2 := q * q", "let qmF := q - F",
    "let G1 := q * qmF", "let G := G1 - C", "let q2m1 := q2 - 1",
    "let Gq := G * q2m1", "let qMF := q * MF", "let MCqMF := MC + qMF",
    "let RJ := MCqMF * J", "let R := Gq + RJ",
):
    assert line in text

# Exact sparse polynomials in beta, J, F, C, MC, MF; q is beta*J+1.
def add(a, b, sign=1):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, 0) + sign * coefficient
    return {m: c for m, c in result.items() if c}

def mul(a, b):
    result = {}
    for x, c in a.items():
        for y, d in b.items():
            m = tuple(i + j for i, j in zip(x, y))
            result[m] = result.get(m, 0) + c * d
    return {m: c for m, c in result.items() if c}

def var(i):
    return {tuple(int(j == i) for j in range(6)): 1}

one = {(0,) * 6: 1}
two = add(one, one)
beta, j, f, c, mc, mf = map(var, range(6))
q = add(mul(beta, j), one)
q2 = mul(q, q)
q3 = mul(q2, q)
q4 = mul(q2, q2)
g = add(mul(q, add(q, f, -1)), c, -1)
rank = add(mul(g, add(q2, one, -1)), mul(add(mc, mul(q, mf)), j))
target = add(add(add(add(q4, q3, -1), q, -1), one, -1), rank, -1)
left = mul(add(mul(q, add(f, one, -1)), add(c, one, -1)), add(q2, one, -1))
middle = mul(add(q, one), add(j, one, -1))
right = mul(j, add(add(add(beta, mc, -1), one, -1),
                   mul(q, add(add(mul(two, beta), mf, -1), one, -1))))
assert target == add(add(left, middle), right)

# Positive witnesses and admissible scalar port bounds can still give R < 0.
b, jj, ff, cc, mm, hh = 31, 1, 100, 1, 30, 32
qq = b * jj + 1
rr = (qq * (qq - ff) - cc) * (qq * qq - 1) + (mm + qq * hh) * jj
assert 0 < jj and 0 < ff and 0 < cc and mm < b < hh < 2 * b
assert rr < 0 and rr + qq**3 + qq + 1 <= qq**4
assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
print(json.dumps({"status": "PASS", "source_sha256": expected,
    "identity": "q^4-q^3-q-1-R = (q(F-1)+C-1)(q^2-1)+(q+1)(J-1)+J((beta-MC-1)+q(2beta-MF-1))",
    "negative_rank_scalar": {"beta": b, "J": jj, "F": ff, "C": cc,
        "MC": mm, "MF": hh, "q": qq, "R": rr},
    "scope": "Exact external polynomial identity and source snippets; no model theorem or graph-zero claim."},
    indent=2, sort_keys=True))
