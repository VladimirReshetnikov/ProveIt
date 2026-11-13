#!/usr/bin/env python3
"""Exact polynomial certificate; no external packages and no Lean invocation."""
import hashlib
import math
import sys
from pathlib import Path

if not (sys.flags.isolated and sys.flags.no_site and sys.flags.optimize == 0):
    raise SystemExit('requires isolated, no-site, non-optimized Python (-I -S, without -O)')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
    ROOT / 'trace75-mask-coordinate-ring-probe/Trace74Mask.lean': '83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0',
    ROOT / 'trace74-guardfree-projection-draft/Trace74GraphProduct.lean': '1a667752791fd01e55abb3c4cbf4bf8b4393d4de3df84bd3a3833d161fe741a6',
    ROOT.parent / 'Lean/DiophantineConsistency/TenPositiveTrace75.lean': '0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',
}
for path, expected in PINS.items():
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
mask = next(iter(PINS)).read_text()
product = list(PINS)[1].read_text()
regs = list(PINS)[2].read_text()
for fragment in ('let h := p 0 * J', 'let X := w * q', 'let H := 4 * Am1 - 1'):
    assert fragment in regs
for fragment in ('let Hp := fourAm1 - 1', 'let Am1 := XY + Y', 'let P1mu2 := bJ * XY'):
    assert fragment in mask
assert 'rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp r))*(ι (Exp.exp r)*rr.X+1)' in product

# Sparse integer polynomials with a single indeterminate, ascending exponents.
def norm(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)
def add(a, b):
    n = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a, neg(b))
def mul(a,b):
    p = [0] * (len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            p[i+j] += x*y
    return norm(p)
def pw(a,n):
    p=(1,)
    for _ in range(n): p=mul(p,a)
    return p
def C(n): return (n,)

y=(0,1)
H=add(add(mul(C(32),pw(y,4)),mul(C(4),y)),C(-1))
# H−35 is a multiple of Y−1; q−1 divides Y−1 when Y=q³.
assert sub(H,C(35)) == mul(sub(y,C(1)),add(mul(C(32),add(add(add(pw(y,3),pw(y,2)),y),C(1))),C(4)))
assert sub(pw(y,3),C(1)) == mul(sub(y,C(1)),add(add(pw(y,2),y),C(1)))
# gcd(H,Y³−4) divides 132Y−1 and the first fixed integer.
f=sub(pw(y,3),C(4)); linear=sub(mul(C(132),y),C(1))
assert sub(H,mul(mul(C(32),y),f)) == linear
first=4*132**3-1
assert sub(mul(C(132**3),f),mul(linear,add(add(pw(mul(C(132),y),2),mul(C(132),y)),C(1)))) == C(-first)
# gcd(H,256Y³+1) divides 31Y−8 and the second fixed integer.
g=add(mul(C(256),pw(y,3)),C(1)); linear2=sub(mul(C(31),y),C(8))
assert sub(mul(C(8),H),mul(y,g)) == linear2
second=31**3+256*8**3
assert sub(mul(C(31**3),g),mul(mul(C(256),linear2),add(add(pw(mul(C(31),y),2),mul(C(8*31),y)),C(64)))) == C(second)
assert first == 9199871 and second == 160863
bound=35*first*second
# q=32+u, u≥0: all coefficients of H(q³)−bound are positive.
q=(32,1); q3=pw(q,3)
shifted=sub(add(add(mul(C(32),pw(q3,4)),mul(C(4),q3)),C(-1)),C(bound))
assert len(shifted)==13 and all(c>0 for c in shifted)
# Exact q=32 check is illustrative; the polynomial certificate above is general.
q0=32; y0=q0**3; x0=8*y0**3; h0=q0-1; H0=32*y0**4+4*y0-1
assert H0>bound and math.gcd(H0,x0)==1
assert 35 % math.gcd(H0,h0)==0
assert first % math.gcd(H0,x0-32)==0
assert second % math.gcd(H0,32*x0+1)==0
assert (h0*x0*(x0-32)*(32*x0+1)) % H0 != 0
print('PASS: pinned sources and exact polynomial/divisibility certificates')
print(f'first={first} second={second} bound={bound} H_at_32={H0}')
print(f'positive_shifted_coefficients={len(shifted)}')
