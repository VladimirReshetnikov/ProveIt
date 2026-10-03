#!/usr/bin/env python3
"""Total quadratic certificates for finite irreversible, exclusive-site systems.

All parameters and witnesses range over N = {0,1,...}.  In timed mode
parameter d_i encodes delay 1+d_i.  No floating-point arithmetic is used.
The exported polynomial is a sum of squares of affine residuals plus
products of nonnegative affine expressions.  It is one quadratic, NOT
an SOS of quadratic residuals.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable
from collections import defaultdict
import json

@dataclass(frozen=True)
class Aff:
    terms: tuple[tuple[str, int], ...] = ()
    const: int = 0
    @staticmethod
    def var(name: str) -> 'Aff':
        return Aff(((name, 1),))
    @staticmethod
    def of(x: 'Aff | int') -> 'Aff':
        return x if isinstance(x, Aff) else Aff((), x)
    def __add__(self, other: 'Aff | int') -> 'Aff':
        o = Aff.of(other); d = dict(self.terms)
        for k, v in o.terms: d[k] = d.get(k, 0) + v
        return Aff(tuple(sorted((k,v) for k,v in d.items() if v)), self.const+o.const)
    __radd__ = __add__
    def __neg__(self) -> 'Aff':
        return Aff(tuple((k,-v) for k,v in self.terms), -self.const)
    def __sub__(self, other: 'Aff | int') -> 'Aff': return self + -Aff.of(other)
    def __rsub__(self, other: 'Aff | int') -> 'Aff': return Aff.of(other) + -self
    def __mul__(self, k: int) -> 'Aff':
        if not isinstance(k, int): raise TypeError('Affine multiplication requires an integer scalar')
        return Aff(tuple((n,v*k) for n,v in self.terms if v*k), self.const*k)
    __rmul__ = __mul__
    def value(self, values: dict[str,int]) -> int:
        return self.const + sum(c*values[n] for n,c in self.terms)
    def data(self) -> dict:
        return {'constant': self.const, 'terms': dict(self.terms)}

@dataclass(frozen=True)
class Rule:
    head: tuple[int,int]
    tail: tuple[tuple[int,int], ...] = ()

@dataclass(frozen=True)
class Network:
    sites: int
    labels: int
    seeds: tuple[tuple[int,int], ...]
    rules: tuple[Rule, ...]
    def validate(self) -> None:
        if self.sites < 0 or self.labels < 1: raise ValueError('Invalid site/label count')
        sd = dict(self.seeds)
        if len(sd) != len(self.seeds): raise ValueError('Repeated seed site')
        def literal(p):
            if not (0 <= p[0] < self.sites and 1 <= p[1] <= self.labels):
                raise ValueError(f'Invalid literal {p}')
        for p in self.seeds: literal(p)
        for r in self.rules:
            literal(r.head)
            if r.head[0] in sd: raise ValueError('Omit rules whose heads are seeded sites')
            if len(set(r.tail)) != len(r.tail): raise ValueError('Duplicate tail literal')
            for p in r.tail: literal(p)

def simulate(net: Network, delays: Iterable[int]) -> tuple[list[int], list[int | None]]:
    """Independent event-driven semantics: earliest completion, label priority."""
    net.validate(); ds = tuple(delays)
    if len(ds) != len(net.rules) or any(not isinstance(x,int) or x<1 for x in ds):
        raise ValueError('Supply one positive integer delay per rule')
    label=[0]*net.sites; time=[None]*net.sites
    for v,a in net.seeds: label[v]=a; time[v]=0
    while True:
        offers=[]
        for r,d in zip(net.rules, ds):
            v,a=r.head
            if label[v] or any(label[u]!=b for u,b in r.tail): continue
            t=max((time[u] for u,b in r.tail), default=0)+d
            offers.append((t,v,a))
        if not offers: return label,time
        now=min(t for t,v,a in offers); batch={}
        for t,v,a in offers:
            if t==now: batch[v]=min(a,batch.get(v,a))
        for v,a in batch.items(): label[v]=a; time[v]=now

class Certificate:
    def __init__(self):
        self.parameters=[]; self.variables=[]; self.residuals=[]; self.products=[]; self.operations=[]
    def new(self, name):
        if name in self.variables or name in self.parameters: raise ValueError('Duplicate variable')
        self.variables.append(name); return Aff.var(name)
    def eq(self, expression): self.residuals.append(Aff.of(expression))
    def prod(self, a,b): self.products.append((Aff.of(a),Aff.of(b)))
    def gate(self, kind, x,y):
        x,y=Aff.of(x),Aff.of(y); i=len(self.operations)
        z=self.new(f'g{i}_z'); a=self.new(f'g{i}_a'); b=self.new(f'g{i}_b')
        if kind=='min': self.eq(x-z-a); self.eq(y-z-b)
        elif kind=='max': self.eq(z-x-a); self.eq(z-y-b)
        else: raise ValueError(kind)
        self.prod(a,b); self.operations.append((kind,z,a,b,x,y)); return z
    def fold(self, kind, xs):
        xs=list(xs)
        if not xs: return Aff.of(0)
        out=xs[0]
        for x in xs[1:]: out=self.gate(kind,out,x)
        return out
    def evaluate(self, values):
        if any(not isinstance(values.get(n),int) or values[n]<0 for n in self.parameters+self.variables):
            raise ValueError('Every parameter and witness must be a natural number')
        return sum(e.value(values)**2 for e in self.residuals)+sum(a.value(values)*b.value(values) for a,b in self.products)
    def expanded(self):
        p=defaultdict(int)
        def mul(a,b):
            ta=list(a.terms)+([('',a.const)] if a.const else [])
            tb=list(b.terms)+([('',b.const)] if b.const else [])
            for x,c in ta:
                for y,d in tb: p[tuple(sorted(n for n in (x,y) if n))]+=c*d
        for e in self.residuals: mul(e,e)
        for a,b in self.products: mul(a,b)
        return {k:v for k,v in p.items() if v}
    def export(self, values=None):
        p=self.expanded()
        result={'domain':'All parameters and witnesses are nonnegative integers.',
                'parameters':self.parameters, 'witnesses':self.variables,
                'affine_residuals':[e.data() for e in self.residuals],
                'nonnegative_products':[[a.data(),b.data()] for a,b in self.products],
                'expanded_polynomial':[{'coefficient':v,'variables':list(k)} for k,v in sorted(p.items(),key=lambda kv:(len(kv[0]),kv[0]))],
                'counts':{'parameters':len(self.parameters),'witnesses':len(self.variables),
                          'affine_residuals':len(self.residuals),'product_terms':len(self.products),
                          'expanded_monomials':len(p),'degree':max(map(len,p),default=0)}}
        if values is not None:
            result['assignment']=values; result['polynomial_value']=self.evaluate(values)
            result['counts']['maximum_witness_bit_length']=max((values[n].bit_length() for n in self.variables),default=0)
        return result

class Compiled:
    def __init__(self, net: Network, timed: bool=True):
        net.validate(); self.net=net; self.timed=timed; self.c=Certificate(); c=self.c
        sd=dict(net.seeds); q=net.labels; B=q+1
        self.free=[v for v in range(net.sites) if v not in sd]
        self.delay=[]; self.prefix=[]
        if timed:
            old=Aff.of(1)
            for j in range(len(net.rules)):
                name=f'delta_{j}'; c.parameters.append(name); d=Aff.var(name)+1
                nxt=c.new(f'cap_{j}'); c.eq(nxt-old-d); self.prefix.append(nxt)
                self.delay.append(d); old=nxt
            self.M=old
        else:
            self.M=Aff.of(len(self.free)+1); self.delay=[Aff.of(1)]*len(net.rules)
        self.t={}; self.l={}
        for v in range(net.sites):
            if v in sd:
                self.t[v]=Aff.of(0)
                for a in range(q+1): self.l[v,a]=Aff.of(int(a==sd[v]))
            else:
                self.t[v]=c.new(f't_{v}')
                for a in range(q+1): self.l[v,a]=c.new(f'l_{v}_{a}')
                c.eq(sum(self.l[v,a] for a in range(q+1))-1)
        self.effective={}; self.mux=[]
        literals=sorted({p for r in net.rules for p in r.tail})
        for u,b in literals:
            if u in sd:
                self.effective[u,b]=Aff.of(0) if sd[u]==b else self.M
            else:
                z=c.new(f'f_{u}_{b}'); a=c.new(f'fa_{u}_{b}'); h=c.new(f'fb_{u}_{b}')
                c.eq(z-self.t[u]-a); c.eq(self.M-z-h)
                c.prod(self.l[u,b],a); c.prod(sum(self.l[u,j] for j in range(q+1) if j!=b),h)
                self.effective[u,b]=z; self.mux.append((u,b,z,a,h))
        offers=defaultdict(list)
        for i,r in enumerate(net.rules):
            tailmax=c.fold('max',[self.effective[p] for p in r.tail])
            offers[r.head].append(tailmax+self.delay[i])
        self.theta={}
        for v in self.free:
            for a in range(1,q+1):
                xs=offers[v,a]
                self.theta[v,a]=c.gate('min',self.M,c.fold('min',xs)) if xs else self.M
        self.gaps=[]
        for v in self.free:
            key=B*self.t[v]+sum(a*self.l[v,a] for a in range(q+1))
            for a in range(q+1):
                cost=B*self.M if a==0 else B*self.theta[v,a]+a
                gap=c.new(f'k_{v}_{a}'); c.eq(cost-key-gap); c.prod(self.l[v,a],gap)
                self.gaps.append((gap,cost,key))
        self.stats={'m':len(self.free),'q':q,'D':len(self.mux),'L':sum(len(r.tail) for r in net.rules),
                    'R':len(net.rules),'R0':sum(not r.tail for r in net.rules)}
        G=self.stats['L']+self.stats['R0']
        assert len(c.operations)==G
        expected=len(self.free)*(2*q+3)+3*len(self.mux)+3*G+(len(net.rules) if timed else 0)
        assert len(c.variables)==expected
    def witness(self, delays=None):
        ds=tuple(delays) if delays is not None else (1,)*len(self.net.rules)
        labels,times=simulate(self.net,ds)
        if not self.timed and any(d!=1 for d in ds): raise ValueError('Unit compiler requires unit delays')
        vals={}
        if self.timed:
            total=1
            for j,d in enumerate(ds): vals[f'delta_{j}']=d-1; total+=d; vals[f'cap_{j}']=total
        M=self.M.value(vals)
        for v in self.free:
            vals[f't_{v}']=M if times[v] is None else times[v]
            for a in range(self.net.labels+1): vals[f'l_{v}_{a}']=int(labels[v]==a)
        def put(aff, value): vals[aff.terms[0][0]]=value
        for u,b,z,a,h in self.mux:
            t=self.t[u].value(vals); f=t if labels[u]==b else M
            put(z,f); put(a,f-t); put(h,M-f)
        for kind,z,a,b,x,y in self.c.operations:
            xx=x.value(vals); yy=y.value(vals); zz=min(xx,yy) if kind=='min' else max(xx,yy)
            put(z,zz)
            put(a,xx-zz if kind=='min' else zz-xx); put(b,yy-zz if kind=='min' else zz-yy)
        for gap,cost,key in self.gaps: put(gap,cost.value(vals)-key.value(vals))
        assert set(vals)==set(self.c.parameters+self.c.variables)
        assert self.c.evaluate(vals)==0
        assert all(vals[x] <= (self.net.labels+1)*(M+1) for x in self.c.variables)
        return vals,labels,times

def save_example(path, net, delays, timed=True):
    comp=Compiled(net,timed=timed); vals,labels,times=comp.witness(delays)
    data=comp.c.export(vals); data['network']={'sites':net.sites,'labels':net.labels,'seeds':net.seeds,
          'rules':[{'head':r.head,'tail':r.tail,'delay':d} for r,d in zip(net.rules,delays)]}
    data['output']={'labels':labels,'times':times}; data['structural_counts']=comp.stats
    with open(path,'w') as f: json.dump(data,f,indent=2)
    return data

class HornCompiled:
    """Smaller q=1 closure compiler. Seeds and catalogue are fixed; no labels needed."""
    def __init__(self, net: Network, timed: bool=False):
        net.validate()
        if net.labels!=1: raise ValueError('Horn specialization requires one label')
        self.net=net; self.timed=timed; self.c=Certificate(); c=self.c
        sd=dict(net.seeds); self.free=[v for v in range(net.sites) if v not in sd]
        self.delay=[]
        if timed:
            old=Aff.of(1)
            for j in range(len(net.rules)):
                name=f'delta_{j}'; c.parameters.append(name); d=Aff.var(name)+1
                nxt=c.new(f'cap_{j}'); c.eq(nxt-old-d); old=nxt; self.delay.append(d)
            self.M=old
        else:
            self.M=Aff.of(len(self.free)+1); self.delay=[Aff.of(1)]*len(net.rules)
        self.t={v:Aff.of(0) if v in sd else c.new(f't_{v}') for v in range(net.sites)}
        offers=defaultdict(list)
        for i,r in enumerate(net.rules):
            offers[r.head[0]].append(c.fold('max',[self.t[u] for u,b in r.tail])+self.delay[i])
        for v in self.free:
            z=c.gate('min',self.M,c.fold('min',offers[v])) if offers[v] else self.M
            c.eq(self.t[v]-z)
        G=sum(len(r.tail) for r in net.rules)+sum(not r.tail for r in net.rules)
        assert len(c.variables)==len(self.free)+3*G+(len(net.rules) if timed else 0)
    def witness(self, delays=None):
        ds=tuple(delays) if delays is not None else (1,)*len(self.net.rules)
        labels,times=simulate(self.net,ds)
        if not self.timed and any(d!=1 for d in ds): raise ValueError('Unit compiler requires unit delays')
        w={}; cap=1
        if self.timed:
            for j,d in enumerate(ds): w[f'delta_{j}']=d-1; cap+=d; w[f'cap_{j}']=cap
        M=self.M.value(w)
        for v in self.free: w[f't_{v}']=M if times[v] is None else times[v]
        def put(a,val): w[a.terms[0][0]]=val
        for kind,z,a,b,x,y in self.c.operations:
            xx=x.value(w); yy=y.value(w); zz=min(xx,yy) if kind=='min' else max(xx,yy)
            put(z,zz); put(a,xx-zz if kind=='min' else zz-xx); put(b,yy-zz if kind=='min' else zz-yy)
        assert self.c.evaluate(w)==0
        return w,labels,times
