def ring(variables, counted=None):
    counted=variables if counted is None else counted
    N=len(variables); zero=(0,)*N
    weights=[counted.get(v,0) if isinstance(counted,dict) else int(v in counted) for v in variables]
    class P:
        def __init__(self,x=0): self.d=dict(x) if isinstance(x,dict) else ({zero:x} if x else {})
        @classmethod
        def var(cls,n):
            e=[0]*N; e[variables.index(n)]=1; return cls({tuple(e):1})
        def __add__(self,b):
            if not isinstance(b,P): b=P(b)
            c=dict(self.d)
            for e,a in b.d.items():
                c[e]=c.get(e,0)+a
                if not c[e]: del c[e]
            return P(c)
        __radd__=__add__
        def __neg__(self): return P({e:-a for e,a in self.d.items()})
        def __sub__(self,b): return self+-b if isinstance(b,P) else self+(-b)
        def __rsub__(self,b): return -self+b
        def __mul__(self,b):
            if not isinstance(b,P): b=P(b)
            c={}
            for e,a in self.d.items():
                for f,b0 in b.d.items():
                    g=tuple(x+y for x,y in zip(e,f)); c[g]=c.get(g,0)+a*b0
            return P({e:a for e,a in c.items() if a})
        __rmul__=__mul__
        def __pow__(self,n):
            a=self; c=P(1)
            while n:
                if n%2: c=c*a
                n//=2
                if n: a=a*a
            return c
        def degree(self): return max((sum(a*b for a,b in zip(e,weights)) for e in self.d),default=-1)
        def lead(self):
            k=self.degree(); return P({e:a for e,a in self.d.items() if sum(x*y for x,y in zip(e,weights))==k})
        def coef(self,powers):
            return self.d.get(tuple(powers.get(n,0) for n in variables),0)
    return P


