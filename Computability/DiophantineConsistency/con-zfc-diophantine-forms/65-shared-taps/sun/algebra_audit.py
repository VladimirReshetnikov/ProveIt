"""Exact elementary algebra checks preserved from package59 Sun verifier."""
from collections import defaultdict
from itertools import product

def require(ok,msg):
    if not ok: raise RuntimeError(msg)

class Poly:
    """Sparse exact integer polynomial, used only on finite local identities."""
    def __init__(self,terms=0):
        self.t=({():terms} if terms else {}) if isinstance(terms,int) else {m:c for m,c in terms.items() if c}
    @staticmethod
    def var(s):return Poly({((s,1),):1})
    def __add__(self,other):
        other=poly(other);d=self.t.copy()
        for m,c in other.t.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o):return self+-poly(o)
    def __rsub__(self,o):return poly(o)+-self
    def __mul__(self,other):
        other=poly(other);d=defaultdict(int)
        for a,c in self.t.items():
            for b,e in other.t.items():
                m=dict(a)
                for s,k in b:m[s]=m.get(s,0)+k
                d[tuple(sorted(m.items()))]+=c*e
        return Poly(dict(d))
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'polynomial power')
        out=Poly(1);x=self
        while n:
            if n&1:out=out*x
            n//=2
            if n:x=x*x
        return out
    def names(self):return {s for m in self.t for s,e in m}
    def __eq__(self,o):return self.t==poly(o).t

def poly(x):return x if isinstance(x,Poly) else Poly(x)

def norm_audit():
    x,a,b,c=[Poly.var(s) for s in ['x','a','b','c']];product_poly=Poly(1)
    for signs in product([-1,1],repeat=3):product_poly*=x+signs[0]*a+signs[1]*b+signs[2]*c
    v=x*x+c*c-a*a-b*b;w=v*v+4*x*x*c*c-4*a*a*b*b
    require(product_poly==w*w-16*v*v*x*x*c*c,'three-radical norm identity')
    return {'status':'PASS','signed_factors':8,'expanded_terms':len(product_poly.t)}

def borrow_audit():
    count=0
    for B in [8,16,32,64,128]:
        for h in range(-B//4+1,B//4):
            for incoming in [-1,0]:
                for selected in [0,1]:
                    v=2*h+selected+incoming
                    require(v//B in [-1,0],'borrow invariant')
                    if selected:
                        require(((v%B)&(B-2)==0)==(h==0),'marked target zero test')
                    count+=1
    require(((-1)%16)&14!=0,'missing target padding negative control')
    return {'status':'PASS','coefficient_transition_cases':count,'tested_bases':[8,16,32,64,128]}

def bitcount_audit():
    total=0
    for u in range(1,8):
        N=1<<u
        for S in range(N):
            for T in range(N-S):
                X=N*N+(S+T)*N+N-1-S;threshold=u+T.bit_count()+1
                require(X.bit_count()==threshold+(S+T).bit_count()-S.bit_count()-T.bit_count(),'bitcount identity')
                require((X.bit_count()>=threshold)==((S&T)==0),'calibrated divisibility')
                total+=1
    return {'status':'PASS','exhaustive_pairs':total,'u_range':[1,7]}

