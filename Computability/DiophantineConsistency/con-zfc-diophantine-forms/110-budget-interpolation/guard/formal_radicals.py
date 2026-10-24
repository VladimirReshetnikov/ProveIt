"""Independent formal radical ring retained from the pinned root-fusion audit."""

ZERO=(0,0,0,0,0,0,0)

class Poly:
    def __init__(self, terms=None):self.terms=terms or {}
    @staticmethod
    def scalar(n):return Poly({ZERO:n}) if n else Poly()
    @staticmethod
    def variable(j):
        m=list(ZERO);m[j]=1;return Poly({tuple(m):1})
    @staticmethod
    def radical(j):
        m=list(ZERO);m[-1]=1<<j;return Poly({tuple(m):1})
    @staticmethod
    def coerce(p):return p if isinstance(p,Poly) else Poly.scalar(p)
    def __add__(self,p):
        p=self.coerce(p);out=dict(self.terms)
        for m,c in p.terms.items():
            out[m]=out.get(m,0)+c
            if not out[m]:del out[m]
        return Poly(out)
    def __radd__(self,p):return self+p
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,p):return self+(-self.coerce(p))
    def __rsub__(self,p):return self.coerce(p)+(-self)
    @staticmethod
    def product_monomial(m,n):
        common=m[6]&n[6]
        return (m[0]+n[0],m[1]+n[1]+(common&1),
          m[2]+n[2]+((common>>1)&1),m[3]+n[3]+((common>>2)&1),
          m[4]+n[4]+((common>>3)&1),m[5]+n[5]+((common>>4)&1),m[6]^n[6])
    def __mul__(self,p):
        p=self.coerce(p);out={};add=out.get;prod=self.product_monomial
        if p is self:
            items=list(self.terms.items())
            for i,(m,c) in enumerate(items):
                u=prod(m,m);out[u]=add(u,0)+c*c
                for n,e in items[i+1:]:
                    u=prod(m,n);out[u]=add(u,0)+2*c*e
        else:
            for m,c in self.terms.items():
                for n,e in p.terms.items():
                    u=prod(m,n);out[u]=add(u,0)+c*e
        return Poly({m:c for m,c in out.items() if c})
    def __rmul__(self,p):return self*p
    def conjugate(self,j):return Poly({m:(-c if m[6]&(1<<j) else c) for m,c in self.terms.items()})
