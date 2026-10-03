#!/usr/bin/env python3
"""New streaming coefficient compiler; no upstream code is imported or executed.

Natural domain, fixed nonempty rectangular prism, threshold six, full exterior
L1 halo. Binary odometers only. See PROOF.md for hypotheses and exact ledgers.
"""
from __future__ import annotations
from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
import argparse, json, math

STEPS=((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))
FIELDS=('z','ell','f','k','c','beta','g','h')
EDGE_FIELDS=('lo','neg','eq','pos','hi','gap')

def natural(v):
    if type(v) is not int or v<0: raise ValueError('expected natural integer')
    return v

def affine(*pairs):
    d=Counter()
    for i,a in pairs:d[i]+=a
    return {i:a for i,a in sorted(d.items()) if a}

def combine(*ds):
    return affine(*(p for d in ds for p in d.items()))

def scale(c,d):return {i:c*a for i,a in d.items() if c*a}
def constant(c):return {-1:c} if c else {}
def var(i):return {i:1}
def triangle(q):return q*(q+1)//2

@dataclass(frozen=True)
class Prism:
    lower:tuple[int,int,int]
    lengths:tuple[int,int,int]
    def __post_init__(self):
        object.__setattr__(self,'lower',tuple(self.lower));object.__setattr__(self,'lengths',tuple(self.lengths))
        if len(self.lower)!=3 or len(self.lengths)!=3:raise ValueError('dimension must be three')
        if any(type(v)is not int for v in self.lower+self.lengths) or min(self.lengths)<1:raise ValueError('invalid prism')
    @property
    def V(self):return math.prod(self.lengths)
    @property
    def S(self):
        a,b,c=self.lengths;return a*b+a*c+b*c
    @property
    def E(self):return 3*self.V-self.S
    @property
    def H(self):return 2*self.S
    @property
    def witnesses(self):return 8*self.V+6*self.E+self.H
    def contains(self,p):return all(l<=x<l+n for x,l,n in zip(p,self.lower,self.lengths))
    def points(self):
        # itertools.product pools each iterable eagerly, which is impossible for
        # literal billion-scale sides. These loops keep range objects lazy.
        a,b,c=self.lengths;l,m,n=self.lower
        for x in range(l,l+a):
            for y in range(m,m+b):
                for z in range(n,n+c):yield x,y,z
    def index(self,p):
        if not self.contains(p):raise ValueError('point outside prism')
        x,y,z=(p[i]-self.lower[i] for i in range(3));a,b,c=self.lengths
        return (x*b+y)*c+z
    def point(self,i):
        if type(i)is not int or not 0<=i<self.V:raise ValueError('bad vertex index')
        a,b,c=self.lengths;x,q=divmod(i,b*c);y,z=divmod(q,c)
        return tuple(self.lower[j]+v for j,v in enumerate((x,y,z)))
    def neighbors(self,p):
        for s in STEPS:
            q=tuple(p[i]+s[i] for i in range(3))
            if self.contains(q):yield q
    def edges(self):
        for axis in range(3):
            dims=list(self.lengths);dims[axis]-=1
            for x in range(dims[0]):
                for y in range(dims[1]):
                    for z in range(dims[2]):
                        off=(x,y,z);p=tuple(off[i]+self.lower[i] for i in range(3));q=list(p);q[axis]+=1
                        yield p,tuple(q)
    def edge_index(self,p,q):
        diff=[i for i in range(3) if p[i]!=q[i]]
        if len(diff)!=1 or abs(p[diff[0]]-q[diff[0]])!=1 or not self.contains(p) or not self.contains(q):raise ValueError('not an internal edge')
        axis=diff[0];lo=min(p,q);a,b,c=self.lengths
        offsets=(0,(a-1)*b*c,(a-1)*b*c+a*(b-1)*c)
        dims=list(self.lengths);dims[axis]-=1
        x,y,z=(lo[i]-self.lower[i] for i in range(3))
        return offsets[axis]+(x*dims[1]+y)*dims[2]+z
    def halo(self):
        for axis in range(3):
            rest=[i for i in range(3) if i!=axis]
            for sign in (-1,1):
                for x in range(self.lengths[rest[0]]):
                    for y in range(self.lengths[rest[1]]):
                        p=list(self.lower);p[axis]+=(-1 if sign==-1 else self.lengths[axis])
                        for i,d in zip(rest,(x,y)):p[i]+=d
                        q=list(p);q[axis]-=sign
                        yield tuple(p),tuple(q)
    def edge_from_index(self,i):
        natural(i)
        if i>=self.E:raise ValueError('bad edge index')
        for axis in range(3):
            dims=list(self.lengths);dims[axis]-=1;n=math.prod(dims)
            if i<n:
                x,t=divmod(i,dims[1]*dims[2]);y,z=divmod(t,dims[2])
                p=tuple(self.lower[j]+d for j,d in enumerate((x,y,z)));q=list(p);q[axis]+=1
                return p,tuple(q)
            i-=n
        raise AssertionError('unreachable')
    def halo_index(self,axis,sign,p):
        rest=[i for i in range(3) if i!=axis]
        offset=sum(2*math.prod(self.lengths[j] for j in range(3) if j!=i) for i in range(axis))
        area=math.prod(self.lengths[j] for j in rest)
        a,b=rest
        return offset+(area if sign==1 else 0)+(p[a]-self.lower[a])*self.lengths[b]+p[b]-self.lower[b]
    def halo_from_index(self,i):
        natural(i)
        if i>=self.H:raise ValueError('bad halo index')
        for axis in range(3):
            rest=[j for j in range(3) if j!=axis];area=math.prod(self.lengths[j] for j in rest)
            if i<2*area:
                side,i=divmod(i,area);sign=-1 if side==0 else 1
                a,b=rest;x,y=divmod(i,self.lengths[b]);p=list(self.lower)
                p[a]+=x;p[b]+=y;p[axis]+=(-1 if sign==-1 else self.lengths[axis]);q=list(p);q[axis]-=sign
                return tuple(p),tuple(q)
            i-=2*area
        raise AssertionError('unreachable')
    def degree_histogram(self):
        d={0:1}
        for a in self.lengths:
            factor={0:1} if a==1 else ({1:2} if a==2 else {1:2,2:a-2})
            out=Counter()
            for i,n in d.items():
                for j,m in factor.items():out[i+j]+=n*m
            d=dict(out)
        return d

@dataclass(frozen=True)
class PeriodicInput:
    periods:tuple[int,int,int]
    table:tuple[int,...]
    additions:tuple[tuple[tuple[int,int,int],int],...]=()
    def __post_init__(self):
        ps=tuple(self.periods);tab=tuple(self.table)
        if len(ps)!=3 or any(type(v)is not int or v<1 for v in ps):raise ValueError('bad period')
        if len(tab)!=math.prod(ps) or any(type(v)is not int or not 0<=v<=5 for v in tab):raise ValueError('background must be stable')
        add={}
        for p,n in self.additions:
            p=tuple(p);natural(n)
            if len(p)!=3 or any(type(v)is not int for v in p):raise ValueError('bad seed coordinate')
            if n:add[p]=add.get(p,0)+n
        object.__setattr__(self,'periods',ps);object.__setattr__(self,'table',tab)
        object.__setattr__(self,'additions',tuple(sorted(add.items())))
    def height(self,p):
        a,b,c=self.periods;x,y,z=(p[i]%self.periods[i] for i in range(3))
        return self.table[(x*b+y)*c+z]+sum(n for q,n in self.additions if p==q)
    def check_prism(self,P):
        if any(not P.contains(p) for p,n in self.additions):raise ValueError('all modifications must be inside the prism')

@dataclass(frozen=True)
class Summand:
    label:str
    kind:str
    residual:dict[int,int]
    weight:dict[int,int]|None=None
    def records(self):
        """Coefficients are emitted before inter-summand collection."""
        r=tuple(self.residual.items())
        if self.kind=='square':
            w=tuple((self.weight or {-1:1}).items())
            for i,(a,ca) in enumerate(r):
                for j in range(i,len(r)):
                    b,cb=r[j];co=ca*cb
                    if i!=j:co*=2
                    for k,ck in w:
                        yield tuple(sorted(v for v in (a,b,k) if v>=0)),co if ck==1 else co*ck
        elif self.kind=='product':
            for a,ca in r:
                for b,cb in self.weight.items():
                    yield tuple(sorted(v for v in (a,b) if v>=0)),ca*cb
        else:raise ValueError('unknown summand kind')
    def value(self,w):
        def ev(d):return sum(c*(1 if i==-1 else w[i]) for i,c in d.items())
        r=ev(self.residual)
        return r*r*(1 if self.weight is None else ev(self.weight)) if self.kind=='square' else r*ev(self.weight)
    def costs(self):
        """Exact costs for PROOF.md's specified affine-evaluation algorithm."""
        q=len(self.residual);qv=sum(i>=0 for i in self.residual)
        w=0 if self.weight is None else len(self.weight)
        wv=0 if self.weight is None else sum(i>=0 for i in self.weight)
        adds=max(0,q-1)+max(0,w-1)
        muls=qv+wv+(1 if self.kind=='product' else 1+int(self.weight is not None))
        raw=triangle(q)*max(1,w) if self.kind=='square' else q*w
        expand_mults=q*q if self.kind=='square' else q*w
        return {'records':raw,'evaluation_adds':adds,'evaluation_mults':muls,'expansion_coefficient_mults':expand_mults}

class Compiler:
    def __init__(self,P,source):
        source.check_prism(P)
        self.P=P;self.source=source
    def v(self,p,f):return 8*self.P.index(p)+FIELDS.index(f)
    def ev(self,p,q,f):return 8*self.P.V+6*self.P.edge_index(p,q)+EDGE_FIELDS.index(f)
    def u(self,p):return affine((self.v(p,'k'),1),(self.v(p,'c'),1))
    def rank(self,p):return affine((self.v(p,'k'),1),(self.v(p,'c'),2),(self.v(p,'beta'),1))
    def comparisons(self,p):
        A={};B={}
        for q in self.P.neighbors(p):
            aa=('eq','pos','hi') if p<q else ('lo','neg','eq')
            bb=('neg','eq','pos','hi') if p<q else ('lo','neg','eq','pos')
            A=combine(A,affine(*((self.ev(p,q,f),1) for f in aa)))
            B=combine(B,affine(*((self.ev(p,q,f),1) for f in bb)))
        return A,B
    def vertex_summands(self,p):
        eta=natural(self.source.height(p));i=self.P.index(p)
        z,ell,f,k,c,beta,g,h=(var(self.v(p,x)) for x in FIELDS)
        A,B=self.comparisons(p)
        def sq(name,r,w=None):return Summand(f'v{i}.{name}','square',r,w)
        def pr(name,l,r):return Summand(f'v{i}.{name}','product',l,r)
        balance=combine(z,scale(6,self.u(p)),*(scale(-1,self.u(q)) for q in self.P.neighbors(p)),constant(-eta))
        yield sq('balance',balance)
        yield sq('stable',combine(z,ell,constant(-5)))
        yield sq('category',combine(f,k,c,constant(-1)))
        yield pr('inactive_beta',combine(f,k),beta)
        yield sq('success',combine(z,scale(-1,A),scale(-1,g)),combine(k,c))
        yield pr('inactive_g',f,g)
        yield sq('previous_failure',combine(B,scale(-1,z),constant(-1),scale(-1,h)),c)
        yield pr('inactive_h',combine(f,k),h)
    def edge_summands(self,p,q):
        e=self.P.edge_index(p,q);lo,neg,eq,pos,hi,gap=(var(self.ev(p,q,f)) for f in EDGE_FIELDS)
        delta=combine(self.rank(q),scale(-1,self.rank(p)))
        yield Summand(f'e{e}.simplex','square',combine(lo,neg,eq,pos,hi,constant(-1)))
        for name,w,r in [('lo',lo,combine(delta,constant(2),gap)),('neg',neg,combine(delta,constant(1))),('eq',eq,delta),('pos',pos,combine(delta,constant(-1))),('hi',hi,combine(delta,constant(-2),scale(-1,gap)))]:
            yield Summand(f'e{e}.{name}','square',r,w)
        yield Summand(f'e{e}.inactive_gap','product',combine(neg,eq,pos),gap)
    def halo_summand(self,j,x,p):
        eta=natural(self.source.height(x))
        if eta>5:raise ValueError('halo is not initially stable')
        gap=var(8*self.P.V+6*self.P.E+j)
        yield Summand(f'h{j}.stable','square',combine(self.u(p),gap,constant(eta-5)))
    def summands(self):
        for p in self.P.points():yield from self.vertex_summands(p)
        for p,q in self.P.edges():yield from self.edge_summands(p,q)
        for j,(x,p) in enumerate(self.P.halo()):yield from self.halo_summand(j,x,p)
    def records(self):
        for term in self.summands():yield from term.records()
    def owner(self,i):
        P=self.P
        if i<8*P.V:return i//8
        if i<8*P.V+6*P.E:return P.index(P.edge_from_index((i-8*P.V)//6)[0])
        return P.index(P.halo_from_index(i-8*P.V-6*P.E)[1])
    def local_summands(self,p):
        yield from self.vertex_summands(p)
        for axis in range(3):
            q=list(p);q[axis]+=1;q=tuple(q)
            if self.P.contains(q):yield from self.edge_summands(p,q)
            for sign in (-1,1):
                if p[axis] == self.P.lower[axis]+(0 if sign==-1 else self.P.lengths[axis]-1):
                    x=list(p);x[axis]+=sign;x=tuple(x)
                    yield from self.halo_summand(self.P.halo_index(axis,sign,p),x,p)
    def collected_records(self):
        """Exactly collected coefficients with <=10738 local raw keys at eta<=6.

        Assign each nonconstant monomial to its least variable-owner vertex.
        Only anchors at that vertex or an adjacent vertex can contribute.
        No full polynomial, global sort, or dense background is materialized.
        """
        P=self.P
        c0=26*P.V+P.E+sum(self.source.height(p)**2 for p in P.points())+sum((self.source.height(x)-5)**2 for x,p in P.halo())
        yield (),c0
        for p in P.points():
            i=P.index(p);bucket=Counter()
            for anchor in (p,*P.neighbors(p)):
                for term in self.local_summands(anchor):
                    for m,c in term.records():
                        if m and min(self.owner(j) for j in m)==i:bucket[m]+=c
            for m,c in sorted(bucket.items()):
                if c:yield m,c
    def collected_statistics(self):
        n=degree=height=0
        for m,c in self.collected_records():n+=1;degree=max(degree,len(m));height=max(height,abs(c))
        return {'collected_monomials':n,'degree':degree,'coefficient_height':height}
    def polynomial(self):
        out=Counter()
        for m,c in self.records():out[m]+=c
        return {m:c for m,c in out.items() if c}
    def evaluate(self,w):
        if len(w)!=self.P.witnesses:raise ValueError('wrong witness count')
        for x in w:natural(x)
        return sum(t.value(w) for t in self.summands())
    def ledger(self,collect=False):
        P=self.P;out=Counter();plain=weighted=products=0
        for t in self.summands():
            out.update(t.costs());out['summands']+=1
            if t.kind=='product':products+=1
            elif t.weight is None:plain+=1
            else:weighted+=1
        out['evaluation_adds']+=out['summands']-1
        out.update({'V':P.V,'E':P.E,'H':P.H,'witnesses':P.witnesses,'plain_square_residuals':plain,'weighted_square_residuals':weighted,'product_summands':products})
        out['coefficient_height_bound']=max(72,12*max((self.source.height(p) for p in P.points()),default=0),max((self.source.height(p)**2 for p in P.points()),default=0))*out['records']
        if collect:
            pol=self.polynomial();out['collected_monomials']=len(pol);out['degree']=max(map(len,pol),default=0);out['coefficient_height']=max(map(abs,pol.values()),default=0)
        return dict(out)
    def closed_ledger(self):
        P=self.P;hist=P.degree_histogram();A=Counter();hlow=0
        for p in P.points():
            if self.source.height(p):A[sum(1 for _ in P.neighbors(p))]+=1
        for x,p in P.halo():hlow+=int(self.source.height(x)<5)
        base=sum(n*(triangle(3+2*d)+21+2*triangle(2+3*d)+triangle(4*d+3)) for d,n in hist.items())
        raw=base+sum(n*(4+2*d) for d,n in A.items())+173*P.E+6*P.H+4*hlow
        return {'V':P.V,'E':P.E,'H':P.H,'witnesses':P.witnesses,'summands':8*P.V+7*P.E+P.H,'plain_square_residuals':3*P.V+P.E+P.H,'weighted_square_residuals':2*P.V+5*P.E,'product_summands':3*P.V+P.E,'records':raw,'evaluation_mults':33*P.V+76*P.E+4*P.H,'evaluation_adds':21*P.V+63*P.E+3*P.H+sum(A.values())+hlow-1,'expansion_coefficient_mults':sum(n*((3+2*d)**2+30+(2+3*d)**2+(3+4*d)**2) for d,n in hist.items())+sum(n*(7+4*d) for d,n in A.items())+301*P.E+9*P.H+7*hlow,'degree_histogram':hist,'nonzero_height_by_degree':dict(A),'halo_height_below_five':hlow}
    def certificate(self):
        """Finite-sink reference constructor for scoped tests, not fast universal execution."""
        P=self.P;points=list(P.points());eta={p:self.source.height(p) for p in points};z=dict(eta);u={p:0 for p in points}
        q=deque(p for p in points if z[p]>=6)
        while q:
            p=q.popleft()
            if z[p]<6:continue
            z[p]-=6;u[p]+=1
            if z[p]>=6:q.append(p)
            if u[p]>1:raise ValueError('sink odometer is not binary')
            for v in P.neighbors(p):
                z[v]+=1
                if z[v]>=6:q.append(v)
        r={p:0 for p in points};remaining={p for p in points if u[p]};round_no=0
        while remaining:
            layer={p for p in remaining if z[p]>=sum(v in remaining for v in P.neighbors(p))}
            if not layer:raise AssertionError('true sink odometer failed burning')
            round_no+=1
            for p in layer:r[p]=round_no
            remaining-=layer
        w=[0]*P.witnesses
        for p in points:
            f,k,c=int(r[p]==0),int(r[p]==1),int(r[p]>=2)
            A=sum(r[v]>=r[p] for v in P.neighbors(p));B=sum(r[v]+1>=r[p] for v in P.neighbors(p))
            vals=(z[p],5-z[p],f,k,c,max(0,r[p]-2),z[p]-A if not f else 0,B-z[p]-1 if c else 0)
            for field,val in zip(FIELDS,vals):w[self.v(p,field)]=val
        for p,v in P.edges():
            d=r[v]-r[p];j=0 if d<=-2 else 1 if d==-1 else 2 if d==0 else 3 if d==1 else 4
            vals=[int(i==j) for i in range(5)]+[max(0,abs(d)-2)]
            for field,val in zip(EDGE_FIELDS,vals):w[self.ev(p,v,field)]=val
        for j,(x,p) in enumerate(P.halo()):
            gap=5-self.source.height(x)-u[p]
            if gap<0:raise ValueError('global exterior halo would be unstable')
            w[8*P.V+6*P.E+j]=gap
        if self.evaluate(w):raise AssertionError('constructed witness did not vanish')
        return w

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--lengths',type=int,nargs=3,default=(1,1,1));ap.add_argument('--background',type=int,default=0);ap.add_argument('--seed',type=int,default=6);ap.add_argument('--stream',action='store_true');ap.add_argument('--collect',action='store_true');args=ap.parse_args()
    P=Prism((0,0,0),tuple(args.lengths));src=PeriodicInput((1,1,1),(args.background,),(((0,0,0),args.seed),));C=Compiler(P,src)
    if args.stream:
        for m,c in C.records():print(json.dumps({'monomial':m,'coefficient':c},separators=(',',':')))
    else:print(json.dumps(C.ledger(args.collect),indent=2,sort_keys=True))
