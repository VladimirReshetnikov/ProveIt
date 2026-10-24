"""Small exact sparse integer-polynomial ring, Python standard library only.

Adapted from the ring used in this contribution's twelve-positive component.
No numerical sampling or external computer-algebra dependency is used.
"""
def require(condition,message):
    if not condition: raise ValueError(message)

class Ring:
    def __init__(self,names,weights=None):
        self.names=list(names); self.n=len(names); self.zero=(0,)*self.n
        self.weights=[1]*self.n if weights is None else list(weights)
    def const(self,k): return Poly(self,{self.zero:k} if k else {})
    def var(self,name):
        e=[0]*self.n; e[self.names.index(name)]=1
        return Poly(self,{tuple(e):1})

class Poly:
    def __init__(self,ring,data): self.ring=ring; self.d=data
    def coerce(self,other):
        if isinstance(other,Poly):
            require(self.ring is other.ring,'Different rings')
            return other
        return self.ring.const(other)
    def __add__(self,other):
        other=self.coerce(other); data=dict(self.d)
        for e,c in other.d.items():
            data[e]=data.get(e,0)+c
            if data[e]==0: del data[e]
        return Poly(self.ring,data)
    __radd__=__add__
    def __neg__(self): return Poly(self.ring,{e:-c for e,c in self.d.items()})
    def __sub__(self,other): return self+-self.coerce(other)
    def __rsub__(self,other): return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other); data={}
        for e,c in self.d.items():
            for f,d in other.d.items():
                g=tuple(x+y for x,y in zip(e,f))
                data[g]=data.get(g,0)+c*d
        return Poly(self.ring,{e:c for e,c in data.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        require(type(n) is int and n>=0,'Bad exponent')
        a=self; out=self.ring.const(1)
        while n:
            if n%2: out=out*a
            n//=2
            if n: a=a*a
        return out
    def degree(self):
        return max((sum(x*w for x,w in zip(e,self.ring.weights)) for e in self.d),default=-1)
    def lead(self):
        deg=self.degree()
        return Poly(self.ring,{e:c for e,c in self.d.items()
            if sum(x*w for x,w in zip(e,self.ring.weights))==deg})

def equal(p,q,label): require(not (p-q).d,'Polynomial mismatch: '+label)

def evaluate(packet,roots,env):
    need=set(roots)
    for name,op,x,y in reversed(packet['source']):
        if name in need and name not in env: need.update((x,y))
    out=dict(env); ring=next(iter(env.values())).ring
    for name,op,x,y in packet['source']:
        if name not in need or name in out: continue
        require(op in ('+','-','*'),'Unknown gate')
        xx=out[x] if isinstance(x,str) else ring.const(x)
        yy=out[y] if isinstance(y,str) else ring.const(y)
        out[name]=xx+yy if op=='+' else xx-yy if op=='-' else xx*yy
    return out

def cut_check(packet,roots,cut_names,formula,label):
    ring=Ring(cut_names); env={name:ring.var(name) for name in cut_names}
    actual=evaluate(packet,roots,env); target=formula(env)
    for name in roots: equal(actual[name],target[name],label+':'+name)
