"""Exact single-fold quartic certificates for parametrized Petri words.

Python 3.10+, standard library only. All polynomial unknowns range over N.
The exported polynomial is the sum of squares of the exported residuals.
Witness recipes are executable constructors, NOT additional polynomial syntax.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping, Iterable
import json

@dataclass(frozen=True)
class Empty:
    pass

@dataclass(frozen=True)
class Atom:
    label: str

@dataclass(frozen=True)
class Concat:
    left: object
    right: object

@dataclass(frozen=True)
class Repeat:
    body: object
    parameter: str

@dataclass(frozen=True)
class Transition:
    take: tuple[int, ...]
    give: tuple[int, ...]
    def __post_init__(self):
        if len(self.take) != len(self.give) or not self.take:
            raise ValueError('Transition vectors must have equal positive dimension')
        if any(type(x) is not int or x < 0 for x in self.take + self.give):
            raise ValueError('Transition weights must be natural numbers')

Summary = tuple[tuple[int, ...], tuple[int, ...]]
Signature = tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]]

def compose(x: Summary, y: Summary) -> Summary:
    u, v = x; a, b = y
    c = tuple(min(s, t) for s, t in zip(v, a))
    return (tuple(s+t-z for s,t,z in zip(u,a,c)),
            tuple(s+t-z for s,t,z in zip(v,b,c)))

def power(x: Summary, k: int) -> Summary:
    if type(k) is not int or k < 0:
        raise ValueError('Exponent must be a natural number')
    u,v=x
    if not k:
        z=(0,)*len(u); return z,z
    c=tuple(min(a,b) for a,b in zip(u,v))
    return (tuple(z+k*(a-z) for a,z in zip(u,c)),
            tuple(z+k*(b-z) for b,z in zip(v,c)))

def independent(x: Transition, y: Transition) -> bool:
    return all(min(uy,vx)==min(ux,vy)
               for ux,vx,uy,vy in zip(x.take,x.give,y.take,y.give))

def independence(net: Mapping[str, Transition]) -> frozenset[tuple[str,str]]:
    return frozenset((a,b) for a in net for b in net
                     if a!=b and independent(net[a],net[b]))

def identity_signature(q: int) -> Signature:
    return 1,(0,)*q,(1,)*q,(0,)*q

def atom_signature(b: str, labels: tuple[str,...], I) -> Signature:
    return (1, tuple(int(a==b) for a in labels),
            tuple(int((a,b) in I and b<a) for a in labels),
            tuple(int((a,b) in I and b>a) for a in labels))

def signature_compose(x: Signature, y: Signature) -> Signature:
    C,R,A,B=x; D,S,E,F=y
    ok=C*D*int(all(not s*b for s,b in zip(S,B)))
    return (ok, tuple(int(r or s*a) for r,s,a in zip(R,S,A)),
            tuple(e*a for e,a in zip(E,A)),
            tuple(e*b+f for e,b,f in zip(E,B,F)))

def signature_power(x: Signature, k: int) -> Signature:
    if not k: return identity_signature(len(x[1]))
    if k==1: return x
    return signature_compose(x,x)

def parameters(e: object) -> set[str]:
    if isinstance(e,(Empty,Atom)): return set()
    if isinstance(e,Concat): return parameters(e.left)|parameters(e.right)
    if isinstance(e,Repeat): return parameters(e.body)|{e.parameter}
    raise TypeError(type(e))

def expanded(e: object, values: Mapping[str,int], limit: int=100000) -> tuple[str,...]:
    if isinstance(e,Empty): return ()
    if isinstance(e,Atom): return (e.label,)
    if isinstance(e,Concat):
        w=expanded(e.left,values,limit)+expanded(e.right,values,limit)
    elif isinstance(e,Repeat):
        k=values[e.parameter]
        if type(k) is not int or k<0: raise ValueError('Invalid exponent')
        if k==0: return ()
        w0=expanded(e.body,values,limit)
        if len(w0)*k>limit: raise OverflowError('Expansion limit exceeded')
        w=w0*k
    else: raise TypeError(type(e))
    if len(w)>limit: raise OverflowError('Expansion limit exceeded')
    return w

def evaluate(e: object, net: Mapping[str,Transition], values: Mapping[str,int], I=None):
    labels=tuple(sorted(net)); p=len(next(iter(net.values())).take)
    I=independence(net) if I is None else I
    if isinstance(e,Empty): return ((0,)*p,(0,)*p),identity_signature(len(labels))
    if isinstance(e,Atom):
        t=net[e.label]; return (t.take,t.give),atom_signature(e.label,labels,I)
    if isinstance(e,Concat):
        x,s=evaluate(e.left,net,values,I); y,t=evaluate(e.right,net,values,I)
        return compose(x,y),signature_compose(s,t)
    if isinstance(e,Repeat):
        x,s=evaluate(e.body,net,values,I); k=values[e.parameter]
        return power(x,k),signature_power(s,k)
    raise TypeError(type(e))

def run(word: Iterable[str], net: Mapping[str,Transition], marking: tuple[int,...]):
    m=marking
    for a in word:
        t=net[a]
        if any(x<y for x,y in zip(m,t.take)): return None
        m=tuple(x-y+z for x,y,z in zip(m,t.take,t.give))
    return m

class Poly:
    """Sparse integer polynomial. Monomials are sorted tuples of variable names."""
    def __init__(self, terms=None):
        self.terms={m:int(c) for m,c in (terms or {}).items() if c}
    @staticmethod
    def cast(x): return x if isinstance(x,Poly) else Poly({():x})
    @staticmethod
    def var(name): return Poly({(name,):1})
    def __add__(self,other):
        d=dict(self.terms)
        for m,c in Poly.cast(other).terms.items(): d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other): return self+-Poly.cast(other)
    def __rsub__(self,other): return Poly.cast(other)+-self
    def __mul__(self,other):
        d={}
        for m,c in self.terms.items():
            for n,e in Poly.cast(other).terms.items():
                key=tuple(sorted(m+n)); d[key]=d.get(key,0)+c*e
        return Poly(d)
    __rmul__=__mul__
    def value(self,env):
        total=0
        for m,c in self.terms.items():
            for name in m: c*=env[name]
            total+=c
        return total
    @property
    def degree(self): return max(map(len,self.terms),default=0)
    def encoded(self):
        return [{'coefficient':c,'monomial':list(m)} for m,c in sorted(self.terms.items())]

class Builder:
    def __init__(self):
        self.inputs=[]; self.recipes=[]; self.residuals=[]
    def parameter(self,name):
        if name not in self.inputs: self.inputs.append(name)
        return Poly.var(name)
    def alloc(self,op,args):
        name=f'w{len(self.recipes):04d}'
        self.recipes.append((name,op,[Poly.cast(a) for a in args]))
        return Poly.var(name)
    def equation(self,a,b=0): self.residuals.append(Poly.cast(a)-b)
    def wire(self,e):
        e=Poly.cast(e); z=self.alloc('eval',[e]); self.equation(z,e); return z
    def bit(self,e):
        z=self.wire(e); self.equation(z*(z-1)); return z
    def AND(self,x,y): return self.bit(x*y)
    def OR(self,x,y): return self.bit(x+y-x*y)
    def NOT(self,x): return self.bit(1-x)
    def all_bits(self,xs):
        z=Poly.cast(1)
        for x in xs: z=self.AND(z,x)
        return z
    def minimum(self,x,y):
        c=self.alloc('min',[x,y]); s=self.alloc('sub',[x,c]); t=self.alloc('sub',[y,c])
        self.equation(c+s,x); self.equation(c+t,y); self.equation(s*t)
        return c,s,t
    def classify(self,k):
        z0=self.alloc('eq0',[k]); z1=self.alloc('eq1',[k]); z2=self.alloc('ge2',[k])
        h=self.alloc('tail2',[k])
        for z in (z0,z1,z2): self.equation(z*(z-1))
        self.equation(z0+z1+z2,1); self.equation(k,z1+2*z2+h)
        self.equation((1-z2)*h)
        return z0,z1,z2
    def construct(self,inputs):
        if set(inputs)!=set(self.inputs):
            raise ValueError(f'Expected inputs {self.inputs}, got {list(inputs)}')
        if any(type(v) is not int or v<0 for v in inputs.values()):
            raise ValueError('All inputs must be natural numbers')
        env=dict(inputs)
        for name,op,args in self.recipes:
            a=[x.value(env) for x in args]
            if op=='eval': v=a[0]
            elif op=='min': v=min(a)
            elif op=='sub': v=a[0]-a[1]
            elif op=='slack': v=max(0,a[0]-a[1])
            elif op=='eq0': v=int(a[0]==0)
            elif op=='eq1': v=int(a[0]==1)
            elif op=='ge2': v=int(a[0]>=2)
            elif op=='tail2': v=max(0,a[0]-2)
            else: raise ValueError(op)
            if v<0: raise ArithmeticError(f'Negative constructed witness at {name}')
            env[name]=v
        return env
    def energy(self,env): return sum(r.value(env)**2 for r in self.residuals)
    def export(self,path):
        obj={'domain':'nonnegative integers','polynomial':'sum_i residual_i^2',
             'inputs':self.inputs,'witnesses':[r[0] for r in self.recipes],
             'residual_degree':max((r.degree for r in self.residuals),default=0),
             'polynomial_degree_upper_bound':4,
             'residuals':[r.encoded() for r in self.residuals],
             'witness_recipes':[{'name':n,'operation':o,'arguments':[p.encoded() for p in a]}
                                for n,o,a in self.recipes]}
        with open(path,'w') as f: json.dump(obj,f,indent=2)

class Compiler:
    def __init__(self,net: Mapping[str,Transition],canonical: bool=False,I=None):
        if not net: raise ValueError('Net must have at least one transition')
        self.net=dict(net); self.labels=tuple(sorted(net)); self.p=len(next(iter(net.values())).take)
        if any(len(t.take)!=self.p for t in net.values()): raise ValueError('Dimension mismatch')
        self.I=independence(net) if I is None else frozenset(I)
        for a,b in self.I:
            if a==b or (b,a) not in self.I or a not in net or b not in net:
                raise ValueError('Independence must be symmetric and irreflexive')
            if not independent(net[a],net[b]): raise ValueError('Unsound independence pair')
        self.canonical=canonical; self.b=Builder(); self._compiled=False
    def cat_resource(self,x,y):
        U,V=x; A,B=y; outU=[];outV=[]
        for u,v,a,b in zip(U,V,A,B):
            c,s,t=self.b.minimum(v,a)
            outU.append(self.b.wire(u+t));outV.append(self.b.wire(b+s))
        return outU,outV
    def pow_resource(self,x,k,z):
        U,V=x; z0,z1,z2=z; active=z1+z2; outU=[];outV=[]
        for u,v in zip(U,V):
            c,a,b=self.b.minimum(u,v)
            outU.append(self.b.wire(active*c+k*a));outV.append(self.b.wire(active*c+k*b))
        return outU,outV
    def cat_signature(self,x,y):
        C,R,A,B=x;D,S,E,F=y; outR=[];outA=[];outB=[];goods=[]
        for r,a,b,s,e,f in zip(R,A,B,S,E,F):
            outR.append(self.b.OR(r,self.b.AND(s,a)))
            outA.append(self.b.AND(e,a))
            outB.append(self.b.bit(self.b.AND(e,b)+f))
            goods.append(self.b.NOT(self.b.AND(s,b)))
        ok=self.b.all_bits([C,D]+goods)
        return ok,outR,outA,outB
    def pow_signature(self,x,z):
        C,R,A,B=x;z0,z1,z2=z;active=z1+z2
        good=self.b.all_bits([self.b.NOT(self.b.AND(r,b)) for r,b in zip(R,B)])
        C2=self.b.AND(C,good)
        C1sel=self.b.AND(z1,C);C2sel=self.b.AND(z2,C2)
        ok=self.b.bit(z0+C1sel+C2sel)
        return (ok,[self.b.bit(active*r) for r in R],
                [self.b.bit(z0+active*a) for a in A],
                [self.b.bit(active*b) for b in B])
    def node(self,e):
        if isinstance(e,(Empty,Atom)):
            if isinstance(e,Empty):
                u=v=(0,)*self.p;s=identity_signature(len(self.labels))
            else:
                t=self.net[e.label];u,v=t.take,t.give;s=atom_signature(e.label,self.labels,self.I)
            res=([self.b.wire(x) for x in u],[self.b.wire(x) for x in v])
            if self.canonical:
                C,R,A,B=s;s=(self.b.bit(C),*[ [self.b.bit(x) for x in xs] for xs in (R,A,B)])
            return res,s
        if isinstance(e,Concat):
            x,s=self.node(e.left);y,t=self.node(e.right)
            return self.cat_resource(x,y),self.cat_signature(s,t) if self.canonical else None
        if isinstance(e,Repeat):
            x,s=self.node(e.body);k=self.b.parameter('k:'+e.parameter);z=self.b.classify(k)
            return self.pow_resource(x,k,z),self.pow_signature(s,z) if self.canonical else None
        raise TypeError(type(e))
    def compile(self,e):
        if self._compiled:
            raise RuntimeError('Use a fresh Compiler for each expression')
        self._compiled=True
        res,s=self.node(e)
        for j,(u,v) in enumerate(zip(*res)):
            m=self.b.parameter(f'm:{j}');n=self.b.parameter(f'n:{j}')
            r=self.b.alloc('slack',[m,u]);self.b.equation(m,u+r);self.b.equation(n,v+r)
        if self.canonical: self.b.equation(s[0],1)
        assert all(r.degree<=2 for r in self.b.residuals)
        return self.b

def word_expression(word: Iterable[str]):
    e=Empty()
    for a in word: e=Concat(e,Atom(a))
    return e

def multiplication_example():
    net={'+':Transition((0,),(1,)), '-':Transition((1,),(0,))}
    body=Repeat(Repeat(word_expression('++'),'x'),'y')
    e=Concat(Concat(body,word_expression('+++')),Repeat(Atom('-'),'z'))
    return net,e

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--export',default='multiplication_certificate.json')
    args=ap.parse_args()
    net,e=multiplication_example();b=Compiler(net).compile(e)
    inp={'k:x':3,'k:y':4,'k:z':27,'m:0':0,'n:0':0}
    env=b.construct(inp); assert b.energy(env)==0
    b.export(args.export)
    print(json.dumps({'inputs':inp,'witnesses':len(b.recipes),'equations':len(b.residuals),
                      'energy':b.energy(env),'output':args.export},indent=2))
