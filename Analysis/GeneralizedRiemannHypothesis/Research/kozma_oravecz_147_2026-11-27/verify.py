"""Independent exact checks. Uses rational endpoints without any rounding."""
from fractions import Fraction as Q

class Box:
    def __init__(self, a, b=None):
        self.a, self.b = Q(a), Q(a if b is None else b)
        assert self.a <= self.b

    @staticmethod
    def cast(x):
        return x if isinstance(x, Box) else Box(x)

    def __add__(x, y):
        y = Box.cast(y)
        return Box(x.a + y.a, x.b + y.b)
    __radd__ = __add__

    def __neg__(x):
        return Box(-x.b, -x.a)

    def __sub__(x, y):
        return x + -Box.cast(y)

    def __mul__(x, y):
        y = Box.cast(y)
        ends = (x.a*y.a, x.a*y.b, x.b*y.a, x.b*y.b)
        return Box(min(ends), max(ends))
    __rmul__ = __mul__

    def inv(x):
        assert x.a > 0
        return Box(1/x.b, 1/x.a)

def poly(x, *cs):
    y = Box(0)
    for c in reversed(cs):
        y = y*x+c
    return y

def U(x):
    return poly(x, -7, 0, 56, 0, -112, 0, 64)

def V(x):
    return poly(x, 0, -8, 0, 8)+x.inv()

def F(x, b):
    return b*poly(x, 0, 112, 0, -448, 0, 384)+poly(x, -8, 0, 24)-(x*x).inv()

def dF(x, b):
    return b*poly(x, 112, 0, -1344, 0, 1920)+48*x+2*(x*x*x).inv()

def bracket(fn, x):
    assert fn(Box(x.a)).b < 0 < fn(Box(x.b)).a

def isolate(fn, x):
    bracket(fn, x)
    lo, hi = x.a, x.b
    while hi-lo > Q(1, 10**42):
        m = (lo+hi)/2
        z = fn(Box(m))
        assert z.a == z.b
        if z.a < 0:
            lo = m
        elif z.b > 0:
            hi = m
        else:
            return Box(m)
    return Box(lo, hi)

B = Box('.92082424565209633887979794209', '.92082424565209633887979794211')
u = Box('.26808235923493042976797397643', '.26808235923493042976797397646')
v = Box('.85459964866741887943600953968', '.85459964866741887943600953971')
x = Box('-.36390801664214987744459', '-.36390801664214987744456')

for t in (u, v):
    bracket(lambda z: F(z, B), t)
    assert dF(t, B).a > 0

def delta(b):
    r, s = (isolate(lambda z: F(z, b), t) for t in (u, v))
    return b*(U(s)-U(r))+V(s)-V(r)

bracket(delta, B)
assert (U(v)-U(u)).a > 0

h, k = u+v, u*v
w = h*h+2*k
c3 = 64*B
c2 = 2*h*c3
c1 = -112*B+2*h*c2-w*c3
c0 = Box(8)+2*h*c1-w*c2+2*h*k*c3
bracket(lambda z: poly(z, c0, c1, c2, c3), x)
L = Box(x.a)
assert c3.a > 0
assert poly(L, c1, 2*c2, 3*c3).a > 0
assert poly(L, 2*c2, 6*c3).a > 0
assert (U(x)-U(u)).a > 0 and (U(v)-U(x)).a > 0

def W3(t):
    return poly(t, 0, -4, 0, 8)

def W6(t):
    return poly(t, -1, 0, 24, 0, -80, 0, 64)

D = (W3(v)-W3(u))*(W6(x)-W6(u))-(W3(x)-W3(u))*(W6(v)-W6(u))
assert Q('4.54') < D.a <= D.b < Q('4.55')
print("All exact checks passed; -0.36390801664214987744459 < xi < -0.36390801664214987744456.")
print("Sine determinant (row order u, v, xi) lies in (4.54, 4.55).")
