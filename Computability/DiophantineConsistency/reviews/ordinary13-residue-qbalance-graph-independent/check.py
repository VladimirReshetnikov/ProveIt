#!/usr/bin/env python3
"""Independent exact polynomial and source-pin check; no Lean execution."""
import hashlib, json
from pathlib import Path
D = Path(__file__).resolve().parent
ROOT = D.parents[1]
PINS = json.loads((D/'pins.json').read_text())
for name, pin in PINS.items():
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == pin, name

# A sparse free commutative polynomial ring over Z, with exact coefficients.
N = 9
class Poly:
    def __init__(self, terms): self.t = {m:c for m,c in terms.items() if c}
    def __add__(self, other):
        other = lift(other); a = dict(self.t)
        for m,c in other.t.items(): a[m] = a.get(m,0)+c
        return Poly(a)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self, other): return self+-lift(other)
    def __rsub__(self, other): return lift(other)+-self
    def __mul__(self, other):
        other=lift(other); a={}
        for m,c in self.t.items():
            for n,d in other.t.items():
                key=tuple(x+y for x,y in zip(m,n)); a[key]=a.get(key,0)+c*d
        return Poly(a)
    __rmul__ = __mul__
    def __eq__(self, other): return self.t == lift(other).t

def lift(n): return n if isinstance(n,Poly) else Poly({(0,)*N:n})
def var(i): return Poly({tuple(int(j==i) for j in range(N)):1})
q,X,s,w,R,gamma,main,c,unused = map(var,range(N))
Y=q*q*q*s; a=X*Y+Y; H=3+4*a; U=Y*q*q
W=4*X*q*s*w; k=R+1+4*X*Y*Y*w
assert 4*X*Y*Y*w == U*W
root = U*main+H*k-U*(X+a*c)-H*(U*gamma+X*Y*q+R+1)
projected = q*(main+H*W)-q*(X+a*c+H*gamma)-H*X
assert root == q*Y*projected
print('Verified pinned sources and exact free-ring scaled-index and oriented-defect identities.')
print('No Lean execution, coordinate-witness binding, provider authentication, or iPRA endpoint is claimed.')
