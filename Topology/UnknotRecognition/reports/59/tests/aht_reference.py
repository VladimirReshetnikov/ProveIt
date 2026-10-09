"""Audit-only extraction of the maintained AHT count path (MIT-0).

Derived from ProveIt fastunknot/interval_orbits.py, Git blob
 e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8, inspected 2026-10-08.
This is NOT a byte-identical snapshot: dataclass/trace/statistics wrappers and
signed-cover helpers are removed; inclusive 5-integer rows are the interface.
It is never silently substituted by sparse_ports.proveit. Small-system tests
compare it to literal union-find; huge periodic fixtures have an independent
analytic answer. No new AHT complexity claim is made for this extraction.
"""
from dataclasses import dataclass
from math import gcd

@dataclass(frozen=True)
class Pair:
    a:int; b:int; c:int; d:int; reverse:bool=False
    def __post_init__(self):
        if any(type(x) is not int or x<0 for x in (self.a,self.b,self.c,self.d)):
            raise ValueError('invalid endpoint')
        if self.a>self.b or self.c>self.d or self.b-self.a != self.d-self.c:
            raise ValueError('invalid pairing')
        if self.a>self.c:
            a,b,c,d=self.c,self.d,self.a,self.b
            for key,value in zip(('a','b','c','d'),(a,b,c,d)):
                object.__setattr__(self,key,value)
    @property
    def identity(self):
        return self.a==self.c and (not self.reverse or self.a==self.b)
    @property
    def periodic(self):
        return not self.reverse and self.a<self.c<=self.b+1


def _contract(n,pairs):
    occupied=[]
    for lo,hi in sorted((lo,hi) for p in pairs
                        for lo,hi in ((p.a,p.b),(p.c,p.d))):
        if occupied and lo<=occupied[-1][1]+1:
            occupied[-1]=(occupied[-1][0],max(hi,occupied[-1][1]))
        else: occupied.append((lo,hi))
    endpoints=sorted({v for p in pairs for v in (p.a,p.b,p.c,p.d)})
    mapping={}; cursor=block=0
    for lo,hi in occupied:
        while cursor<len(endpoints) and endpoints[cursor]<=hi:
            old=endpoints[cursor]; mapping[old]=block+old-lo; cursor+=1
        block+=hi-lo+1
    return block,[Pair(*(mapping[v] for v in (p.a,p.b,p.c,p.d)),p.reverse)
                   for p in pairs],n-block


def count_orbits(n,rows,*,cycle_cap=None):
    if type(n) is not int or n<0: raise ValueError('invalid size')
    pairs=[]
    for a,b,c,d,sign in rows:
        if sign not in (-1,1) or type(sign) is not int: raise ValueError('sign')
        p=Pair(a,b,c,d,sign==-1)
        if p.d>=n: raise ValueError('pairing outside universe')
        pairs.append(p)
    total=cycles=0
    while n:
        if cycle_cap is not None and cycles>=cycle_cap:
            raise RuntimeError('audit AHT cycle cap reached')
        cycles+=1
        pairs=[p for p in pairs if not p.identity]
        if not pairs:
            total+=n; break
        n,pairs,removed=_contract(n,pairs); total+=removed
        for i,p in enumerate(pairs):
            if p.reverse and p.b>=p.c:
                twice=p.a+p.d
                pairs[i]=Pair(p.a,(twice-1)//2,twice//2+1,p.d,True)
        while True:
            found=False
            for i,p in enumerate(pairs):
                if not p.periodic: continue
                for j in range(i+1,len(pairs)):
                    q=pairs[j]
                    if not q.periodic: continue
                    u,v=p.c-p.a,q.c-q.a; common=gcd(u,v)
                    if min(p.d,q.d)-max(p.a,q.a)+1 < u+v-common: continue
                    lo,hi=min(p.a,q.a),max(p.d,q.d)
                    pairs[i]=Pair(lo,hi-common,lo+common,hi)
                    pairs.pop(j);found=True;break
                if found:break
            if not found:break
        index=max(range(len(pairs)),key=lambda i:(pairs[i].d,-pairs[i].c,
                                                  -pairs[i].a,int(pairs[i].reverse)))
        carrier=pairs[index]
        for i,p in enumerate(pairs):
            if i==index or not carrier.c<=p.c<=p.d<=carrier.d:continue
            domain=carrier.c<=p.a<=p.b<=carrier.d
            if carrier.reverse:
                twice=carrier.a+carrier.d
                c,d=twice-p.d,twice-p.c
                a,b=(twice-p.b,twice-p.a) if domain else (p.a,p.b)
                reverse=p.reverse ^ True ^ domain
            else:
                period=carrier.c-carrier.a
                t=(p.c-carrier.c)//period+1
                c,d=p.c-t*period,p.d-t*period
                if domain:
                    s=(p.a-carrier.c)//period+1
                    a,b=p.a-s*period,p.b-s*period
                else:a,b=p.a,p.b
                reverse=p.reverse
            pairs[i]=Pair(a,b,c,d,reverse)
        cut=max([carrier.c]+[p.d+1 for i,p in enumerate(pairs) if i!=index])
        if not carrier.c<=cut<n or carrier.d!=n-1:
            raise AssertionError('AHT suffix not exposed')
        removed=n-cut
        if cut==carrier.c:pairs.pop(index)
        elif carrier.reverse:
            pairs[index]=Pair(carrier.a+removed,carrier.b,carrier.c,cut-1,True)
        else:pairs[index]=Pair(carrier.a,carrier.b-removed,carrier.c,cut-1)
        n=cut
    return total


class LiteralSystem:
    def __init__(self,n,rows):
        self.n=n; self.parent=list(range(n))
        for a,b,c,d,sign in rows:
            for x in range(a,b+1):
                self.join(x,a+d-x if sign==-1 else x+c-a)
    def root(self,x):
        while self.parent[x]!=x:
            self.parent[x]=self.parent[self.parent[x]];x=self.parent[x]
        return x
    def join(self,x,y):
        self.parent[self.root(x)]=self.root(y)
    def count(self):
        return len({self.root(x) for x in range(self.n)})
    def histogram(self,ports):
        masks={self.root(x):0 for x in range(self.n)}
        for i,port in enumerate(ports):
            for lo,hi in port:
                for x in range(lo,hi):masks[self.root(x)] |= 1<<i
        hist={}
        for mask in masks.values():hist[mask]=hist.get(mask,0)+1
        return hist


def periodic_histogram(period,ports):
    """Independent endpoint sweep of mark projections modulo period."""
    events={0:[],period:[]}
    for i,port in enumerate(ports):
        for lo,hi in port:
            length=hi-lo
            if length>=period: pieces=[(0,period)]
            elif length==0:pieces=[]
            else:
                start=lo%period;end=start+length
                pieces=[(start,min(end,period))]
                if end>period:pieces.append((0,end-period))
            for a,b in pieces:
                events.setdefault(a,[]).append((i,1))
                events.setdefault(b,[]).append((i,-1))
    counts=[0]*len(ports);result={};last=0;mask=0
    for point in sorted(events):
        if point>last:result[mask]=result.get(mask,0)+point-last
        for i,delta in events[point]:
            counts[i]+=delta
            if counts[i]:mask|=1<<i
            else:mask &= ~(1<<i)
        last=point
    return result
