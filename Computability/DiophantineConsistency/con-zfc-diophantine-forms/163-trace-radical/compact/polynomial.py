"""Sparse integer polynomial arithmetic retained with attribution.

Adapted verbatim from inherited/lucas/parent/verify.py, which credits the
Centered Residues source. No producer is imported by the checker.
"""
class Poly:
    def __init__(self, x=0):
        self.d = x if isinstance(x, dict) else ({} if x == 0 else {(): x})
    @staticmethod
    def v(name):
        return Poly({((name, 1),): 1})
    def __add__(self, other):
        other = aspoly(other)
        d = dict(self.d)
        for m, c in other.d.items():
            d[m] = d.get(m, 0) + c
            if not d[m]: del d[m]
        return Poly(d)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self, other): return self + -aspoly(other)
    def __rsub__(self, other): return aspoly(other) + -self
    def __mul__(self, other):
        other=aspoly(other); d={}
        for m,c in self.d.items():
            for n,e in other.d.items():
                powers=dict(m)
                for v,k in n: powers[v]=powers.get(v,0)+k
                z=tuple(sorted(powers.items()))
                d[z]=d.get(z,0)+c*e
                if not d[z]: del d[z]
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        if n < 0: raise ValueError("negative exponent")
        ans=Poly(1); x=self
        while n:
            if n&1: ans=ans*x
            x=x*x; n//=2
        return ans
    def __eq__(self,other): return self.d==aspoly(other).d
    def serial(self): return [{"powers":dict(m),"coefficient":c} for m,c in sorted(self.d.items())]

def aspoly(x): return x if isinstance(x,Poly) else Poly(x)
def require(test,message):
    if not test: raise ValueError(message)

