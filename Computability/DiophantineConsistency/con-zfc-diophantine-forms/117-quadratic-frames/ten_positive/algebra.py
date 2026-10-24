"""Small exact sparse-polynomial oracle; standard library only."""
class Poly:
    dim=6
    def __init__(self,value=0):
        if isinstance(value,Poly): self.t=dict(value.t)
        elif isinstance(value,dict): self.t={m:c for m,c in value.items() if c}
        else:self.t={} if value==0 else {(0,)*self.dim:value}
    def __add__(self,other):
        other=Poly(other); d=dict(self.t)
        for m,c in other.t.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,other):return self+-Poly(other)
    def __rsub__(self,other):return Poly(other)+-self
    def __mul__(self,other):
        other=Poly(other); d={}
        for m,c in self.t.items():
            for n,b in other.t.items():
                k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        if type(n)is not int or n<0:raise ValueError('nonnegative integer exponent required')
        out=Poly(1);x=self
        while n:
            if n&1:out=out*x
            n//=2
            if n:x=x*x
        return out
    def __eq__(self,other):return self.t==Poly(other).t
    def degree(self):return max((sum(m) for m in self.t),default=-1)
    def weighted_degree(self,weights):return max((sum(a*b for a,b in zip(m,weights)) for m in self.t),default=-1)

def variable(j):return Poly({tuple(int(i==j) for i in range(Poly.dim)):1})

def variables(n):
    Poly.dim=n
    return [variable(i) for i in range(n)]

def evaluate(rows,inputs,modulus=None):
    env=dict(inputs)
    for name,op,a,b in rows:
        a=a if type(a)is int else env[a]
        b=b if type(b)is int else env[b]
        value=a+b if op=='+' else a-b if op=='-' else a*b
        env[name]=value if modulus is None else value%modulus
    return env

def expand_cut(rows,register,leaves):
    defs={r[0]:r[1:] for r in rows};memo=dict(leaves)
    def go(v):
        if type(v)is int:return Poly(v)
        if v in memo:return memo[v]
        op,a,b=defs[v];a,b=go(a),go(b)
        memo[v]=a+b if op=='+' else a-b if op=='-' else a*b
        return memo[v]
    return go(register)
