"""Minimal exact multivariate integer polynomial arithmetic for audits."""
class Poly:
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms=value.terms.copy()
        elif isinstance(value,int):
            self.terms={} if value==0 else {():value}
        elif isinstance(value,dict):
            self.terms={m:c for m,c in value.items() if c}
        else:
            raise TypeError(type(value))
    @staticmethod
    def var(name):
        return Poly({((name,1),):1})
    def __add__(self,other):
        other=Poly(other)
        out=self.terms.copy()
        for m,c in other.terms.items(): out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other): return self+-Poly(other)
    def __rsub__(self,other): return Poly(other)+-self
    def __mul__(self,other):
        other=Poly(other)
        out={}
        for m,c in self.terms.items():
            for n,d in other.terms.items():
                p=dict(m)
                for v,k in n: p[v]=p.get(v,0)+k
                key=tuple(sorted(p.items()))
                out[key]=out.get(key,0)+c*d
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        result=Poly(1)
        base=self
        while n:
            if n&1: result=result*base
            base=base*base
            n//=2
        return result
    def __eq__(self,other): return self.terms==Poly(other).terms
    @property
    def symbols(self): return {v for m in self.terms for v,k in m}
    def degree(self,variables):
        variables=set(variables)
        return max((sum(e for v,e in m if v in variables) for m in self.terms),default=-1)
    def substitute(self,mapping):
        total=Poly(0)
        for m,c in self.terms.items():
            term=Poly(c)
            for v,e in m: term*=mapping.get(v,Poly.var(v))**e
            total+=term
        return total
    def __str__(self):
        if not self.terms: return '0'
        pieces=[]
        for m,c in sorted(self.terms.items(),key=lambda item:(-sum(e for v,e in item[0]),item[0])):
            factors=[v if e==1 else f'{v}**{e}' for v,e in m]
            if abs(c)!=1 or not factors: factors.insert(0,str(abs(c)))
            term='*'.join(factors)
            if not pieces: pieces.append(('-' if c<0 else '')+term)
            else: pieces.append((' - ' if c<0 else ' + ')+term)
        return ''.join(pieces)
