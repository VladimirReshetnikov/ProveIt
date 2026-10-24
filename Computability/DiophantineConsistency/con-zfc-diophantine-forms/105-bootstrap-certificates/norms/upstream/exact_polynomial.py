"""Small independent sparse integer polynomial ring; no external dependency."""

class Ring:
    def __init__(self,names):
        self.names=tuple(names);self.zero=(0,)*len(names)
    def scalar(self,n):return Poly(self,{self.zero:n} if n else {})
    def var(self,name):
        m=list(self.zero);m[self.names.index(name)]=1;return Poly(self,{tuple(m):1})
    def monomial(self,exponents,coefficient=1):return Poly(self,{tuple(exponents):coefficient})

class Poly:
    def __init__(self,ring,terms=None):self.ring,self.terms=ring,terms or {}
    def coerce(self,q):
        if isinstance(q,Poly):
            if q.ring is not self.ring:raise ValueError('different rings')
            return q
        if not isinstance(q,int):raise ValueError('integer coefficient required')
        return self.ring.scalar(q)
    def __add__(self,q):
        q=self.coerce(q);out=dict(self.terms)
        for m,c in q.terms.items():
            out[m]=out.get(m,0)+c
            if not out[m]:del out[m]
        return Poly(self.ring,out)
    def __radd__(self,q):return self+q
    def __neg__(self):return Poly(self.ring,{m:-c for m,c in self.terms.items()})
    def __sub__(self,q):return self+(-self.coerce(q))
    def __rsub__(self,q):return self.coerce(q)+(-self)
    def __mul__(self,q):
        q=self.coerce(q);out={}
        if q is self:
            a=list(self.terms.items())
            for i,(m,c) in enumerate(a):
                u=tuple(2*x for x in m);out[u]=out.get(u,0)+c*c
                for n,e in a[i+1:]:
                    u=tuple(x+y for x,y in zip(m,n));out[u]=out.get(u,0)+2*c*e
        else:
            for m,c in self.terms.items():
                for n,e in q.terms.items():
                    u=tuple(x+y for x,y in zip(m,n));out[u]=out.get(u,0)+c*e
        return Poly(self.ring,{m:c for m,c in out.items() if c})
    def __rmul__(self,q):return self*q
    def __pow__(self,n):
        if not isinstance(n,int) or n<0:raise ValueError('fixed nonnegative exponent')
        if n==0:return self.ring.scalar(1)
        if n==1:return self
        a=self**(n//2);return a*a if n%2==0 else a*a*self
    def weighted_degree(self,weights):
        return max((sum(a*b for a,b in zip(m,weights)) for m in self.terms),default=-1)
    def homogeneous(self,weights,degree):
        return {m:c for m,c in self.terms.items() if sum(a*b for a,b in zip(m,weights))==degree}
