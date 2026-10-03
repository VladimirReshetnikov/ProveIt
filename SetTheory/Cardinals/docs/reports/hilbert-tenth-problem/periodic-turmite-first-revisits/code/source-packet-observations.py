"""Exact first-hit queries for certified one-visit turmite paths.
No third-party dependencies, time enumeration, or general Presburger solver.
All public IndexSet constructors preserve a Boolean indicator invariant.
"""
from dataclasses import dataclass
from math import gcd, lcm
from types import MappingProxyType
from one_visit import Lane, Result, decide, egcd, ceildiv, snapshot_head


def integer(x,name):
    if not isinstance(x,int): raise ValueError(name+' must be an integer')
    return x


@dataclass(frozen=True)
class Progression:
    first: int
    last: int | None
    step: int
    def __post_init__(self):
        integer(self.first,'first'); integer(self.step,'step')
        if self.first<0 or self.step<1: raise ValueError('Invalid progression')
        if self.last is not None:
            integer(self.last,'last')
            if self.last<self.first or (self.last-self.first)%self.step:
                raise ValueError('Invalid progression endpoint')
            if self.last==self.first and self.step!=1:
                raise ValueError('Singleton progression must have step 1')
    def count(self,lo,hi):
        lo=max(lo,self.first)
        if self.last is not None: hi=min(hi,self.last)
        if hi<lo: return 0
        start=lo+(self.first-lo)%self.step
        return 0 if start>hi else (hi-start)//self.step+1
    def contains(self,n):
        return n>=self.first and (self.last is None or n<=self.last) and (n-self.first)%self.step==0


def atom(lo=0,hi=None,residue=0,modulus=1):
    """Canonical interval-congruence atom, or None for empty."""
    for x,name in ((lo,'lo'),(residue,'residue'),(modulus,'modulus')): integer(x,name)
    if hi is not None: integer(hi,'hi')
    if modulus<=0: raise ValueError('Modulus must be positive')
    lo=max(0,lo)
    first=lo+(residue-lo)%modulus
    if hi is not None:
        if first>hi: return None
        hi-= (hi-residue)%modulus
        if first==hi: modulus=1
    return Progression(first,hi,modulus)


def intersect(a,b):
    """Generalized CRT, including non-coprime moduli and finite cutoffs."""
    if a is None or b is None: return None
    g=gcd(a.step,b.step); difference=b.first-a.first
    if difference%g: return None
    reduced=b.step//g
    k=0 if reduced==1 else ((difference//g)*pow(a.step//g,-1,reduced))%reduced
    modulus=a.step*reduced
    residue=(a.first+a.step*k)%modulus
    hi=b.last if a.last is None else a.last if b.last is None else min(a.last,b.last)
    return atom(max(a.first,b.first),hi,residue,modulus)


class IndexSet:
    """A set of nonnegative indices, represented by a trusted signed indicator sum.
    Do not manually inject coefficients: zero-count emptiness relies on Booleanity.
    Public construction takes only a single validated atom (or None = empty).
    """
    def __init__(self,a=None):
        if a is not None and not isinstance(a,Progression):
            raise ValueError('IndexSet requires a Progression or None')
        self._terms=MappingProxyType({} if a is None else {a:1})
    @classmethod
    def _trusted(cls,terms):
        obj=object.__new__(cls)
        obj._terms=MappingProxyType({a:c for a,c in terms.items() if c})
        return obj
    @property
    def terms(self): return tuple(self._terms.items())
    def __and__(self,other):
        if not isinstance(other,IndexSet): return NotImplemented
        terms={}
        for a,c in self._terms.items():
            for b,d in other._terms.items():
                ab=intersect(a,b)
                if ab is not None: terms[ab]=terms.get(ab,0)+c*d
        return self._trusted(terms)
    def __invert__(self):
        terms={Progression(0,None,1):1}
        for a,c in self._terms.items(): terms[a]=terms.get(a,0)-c
        return self._trusted(terms)
    def __or__(self,other):
        if not isinstance(other,IndexSet): return NotImplemented
        terms=dict(self._terms)
        for a,c in other._terms.items(): terms[a]=terms.get(a,0)+c
        for a,c in (self&other)._terms.items(): terms[a]=terms.get(a,0)-c
        return self._trusted(terms)
    def contains(self,n):
        integer(n,'index')
        if n<0: return False
        val=sum(c for a,c in self._terms.items() if a.contains(n))
        if val not in (0,1): raise RuntimeError('Boolean indicator invariant broken')
        return bool(val)
    def count(self,lo,hi):
        integer(lo,'lo'); integer(hi,'hi')
        lo=max(0,lo)
        if hi<lo: return 0
        val=sum(c*a.count(lo,hi) for a,c in self._terms.items())
        if not 0<=val<=hi-lo+1: raise RuntimeError('Boolean count invariant broken')
        return val
    def eventual_bound(self):
        """Return B,Q: indicator is Q-periodic for all n>=B."""
        B=0; Q=1
        for a in self._terms:
            if a.last is None: B=max(B,a.first); Q=lcm(Q,a.step)
            else: B=max(B,a.last+1)
        return B,Q
    def minimum(self):
        B,Q=self.eventual_bound(); high=B+Q-1
        if self.count(0,high)==0: return None
        low=0
        while low<high:
            mid=(low+high)//2
            if self.count(0,mid)>0: high=mid
            else: low=mid+1
        return low


def indices(lo=0,hi=None,residue=0,modulus=1):
    return IndexSet(atom(lo,hi,residue,modulus))


def empty(): return IndexSet()
def universe(): return indices()


def union(sets):
    answer=empty()
    for s in sets: answer=answer|s
    return answer


def linear_congruence(coefficient,rhs,modulus):
    for x,name in ((coefficient,'coefficient'),(rhs,'rhs'),(modulus,'modulus')): integer(x,name)
    if modulus<=0: raise ValueError('Modulus must be positive')
    g=gcd(coefficient,modulus)
    if rhs%g: return empty()
    q=modulus//g
    residue=0 if q==1 else ((rhs//g)*pow(coefficient//g,-1,q))%q
    return indices(residue=residue,modulus=q)


def validate_lane(a):
    if not isinstance(a,Lane): raise ValueError('Expected Lane')
    for p in (a.p,a.d):
        if not isinstance(p,tuple) or len(p)!=2 or not all(isinstance(z,int) for z in p):
            raise ValueError('Lane vectors must be integer pairs')
    integer(a.t,'time'); integer(a.period,'period')
    if a.period<=0: raise ValueError('Lane period must be positive')
    if a.last is not None:
        integer(a.last,'last')
        if a.last<0: raise ValueError('Lane endpoint must be nonnegative')


def relation_indices(new,old,chronological=True):
    """All new indices n with a spatially matching old index k (strictly past if requested)."""
    validate_lane(new); validate_lane(old)
    a,b=new.d[0],-old.d[0]; c,d=new.d[1],-old.d[1]
    e,f=old.p[0]-new.p[0],old.p[1]-new.p[1]
    def valid(n,k):
        return (n>=0 and k>=0 and (new.last is None or n<=new.last)
                and (old.last is None or k<=old.last)
                and (not chronological or new.time(n)>old.time(k)))
    determinant=a*d-b*c
    if determinant:
        nn,kk=e*d-b*f,a*f-e*c
        if nn%determinant or kk%determinant: return empty()
        n,k=nn//determinant,kk//determinant
        return indices(n,n) if valid(n,k) else empty()
    if a==b==c==d==0:
        if e or f: return empty()
        lower=0 if not chronological else max(0,ceildiv(old.t+1-new.t,new.period))
        return indices(lower,new.last)
    if a==b==0: a,b,e,c,d,f=c,d,f,a,b,e
    g,x,y=egcd(a,b)
    if e%g: return empty()
    n0,k0=x*(e//g),y*(e//g); sn,sk=b//g,-a//g
    if c*n0+d*k0!=f or c*sn+d*sk!=0: return empty()
    low=high=None
    def add_lower(constant,coefficient):
        nonlocal low,high
        if coefficient>0:
            bound=ceildiv(-constant,coefficient); low=bound if low is None else max(low,bound)
        elif coefficient<0:
            bound=constant//(-coefficient); high=bound if high is None else min(high,bound)
        elif constant<0: return False
        return low is None or high is None or low<=high
    constraints=[(n0,sn),(k0,sk)]
    if new.last is not None: constraints.append((new.last-n0,-sn))
    if old.last is not None: constraints.append((old.last-k0,-sk))
    if chronological:
        constraints.append((new.t+new.period*n0-old.t-old.period*k0-1,
                            new.period*sn-old.period*sk))
    if not all(add_lower(*constraint) for constraint in constraints): return empty()
    if sn==0: return indices(n0,n0)
    if sn>0:
        if low is None: raise RuntimeError('Missing nonnegative-index lower bound')
        first=n0+sn*low; last=None if high is None else n0+sn*high
    else:
        if high is None: raise RuntimeError('Missing nonnegative-index upper bound')
        first=n0+sn*high; last=None if low is None else n0+sn*low
    return indices(first,last,n0,abs(sn))


@dataclass(frozen=True)
class Clause:
    """Conjunction. None headings/sites means unrestricted; empty means impossible.
    congruences entries = (x coefficient, y coefficient, residue, positive modulus).
    stencil entries = (dx,dy,colour); duplicates, including contradictions, are meaningful.
    """
    headings: tuple | None = None
    congruences: tuple = ()
    sites: tuple | None = None
    stencil: tuple = ()
    def __post_init__(self):
        # Materialize finite iterables exactly once: validation must not consume a query.
        try:
            if self.headings is not None: object.__setattr__(self,'headings',tuple(self.headings))
            object.__setattr__(self,'congruences',tuple(tuple(item) for item in self.congruences))
            if self.sites is not None: object.__setattr__(self,'sites',tuple(tuple(p) for p in self.sites))
            object.__setattr__(self,'stencil',tuple(tuple(item) for item in self.stencil))
        except TypeError as error:
            raise ValueError('Clause fields must be finite iterables of the documented shapes') from error


@dataclass(frozen=True)
class Hit:
    time: int
    position: tuple
    heading: int
    clause_index: int
    lane_index: int
    lane_index_value: int


def validate_clause(clause,m):
    if not isinstance(clause,Clause): raise ValueError('Expected Clause')
    if clause.headings is not None and not all(isinstance(h,int) and 0<=h<4 for h in clause.headings):
        raise ValueError('Invalid allowed heading')
    for item in clause.congruences:
        if len(item)!=4 or not all(isinstance(x,int) for x in item) or item[3]<=0:
            raise ValueError('Invalid coordinate congruence')
    if clause.sites is not None:
        if not all(len(p)==2 and all(isinstance(z,int) for z in p) for p in clause.sites):
            raise ValueError('Invalid finite head-site restriction')
    for item in clause.stencil:
        if len(item)!=3 or not all(isinstance(x,int) for x in item) or not 0<=item[2]<m:
            raise ValueError('Invalid stencil entry')


def shifted(a,offset):
    return Lane((a.p[0]+offset[0],a.p[1]+offset[1]),a.d,a.t,a.period,a.last,a.heading)


def point_indices(a,p):
    return relation_indices(a,Lane(tuple(p),(0,0),0,1,0),False)


def initial_colour_indices(a,colour,tile,defects):
    u,v=len(tile[0]),len(tile)
    defective=empty(); matching_defects=empty()
    for p,c in defects.items():
        here=point_indices(a,p); defective=defective|here
        if c==colour: matching_defects=matching_defects|here
    background=empty()
    for y,row in enumerate(tile):
        for x,c in enumerate(row):
            if c==colour:
                here=(linear_congruence(a.d[0],x-a.p[0],u)
                      &linear_congruence(a.d[1],y-a.p[1],v))
                background=background|here
    return matching_defects|((~defective)&background)


def clause_indices(a,clause,result,rule,tile,defects):
    """Compile one lane/clause into the exact nonnegative index set."""
    validate_lane(a); validate_clause(clause,len(rule))
    answer=indices(0,a.last)
    if clause.headings is not None and a.heading not in clause.headings: return empty()
    for cx,cy,r,q in clause.congruences:
        answer=answer&linear_congruence(cx*a.d[0]+cy*a.d[1],r-cx*a.p[0]-cy*a.p[1],q)
    if clause.sites is not None:
        answer=answer&union(point_indices(a,p) for p in clause.sites)
    cache={}
    for dx,dy,colour in clause.stencil:
        offset=(dx,dy); loc=shifted(a,offset)
        if offset not in cache:
            cache[offset]=union(relation_indices(loc,b,True) for b in result.lanes)
        visited=cache[offset]
        before=initial_colour_indices(loc,colour,tile,defects)
        after=initial_colour_indices(loc,(colour-1)%len(rule),tile,defects)
        answer=answer&((before&~visited)|(after&visited))
    return answer


def first_hit(result,rule,tile,defects,clauses):
    """Query a Result created from these same inputs by decide().
    Do not supply an arbitrary or mismatched Result: the certified-path precondition matters.
    First repeated arrival is included; no post-repeat claim is made.
    """
    if not isinstance(result,Result): raise ValueError('Expected a certified Result')
    # Explicit input validation independent of Python optimization mode.
    if not isinstance(rule,str) or not rule or not set(rule)<=set('LR'):
        raise ValueError('Invalid rule')
    if not tile or not tile[0] or not all(len(row)==len(tile[0]) for row in tile):
        raise ValueError('Invalid tile')
    if not all(isinstance(c,int) and 0<=c<len(rule) for row in tile for c in row):
        raise ValueError('Invalid tile colour')
    defects=dict(defects or {}); clauses=tuple(clauses)
    if not all(isinstance(p,tuple) and len(p)==2 and all(isinstance(z,int) for z in p)
               and isinstance(c,int) and 0<=c<len(rule) for p,c in defects.items()):
        raise ValueError('Invalid defect')
    for clause in clauses: validate_clause(clause,len(rule))
    best=None
    for i,a in enumerate(result.lanes):
        for j,clause in enumerate(clauses):
            n=clause_indices(a,clause,result,rule,tile,defects).minimum()
            if n is not None:
                hit=Hit(a.time(n),a.point(n),a.heading,j,i,n)
                if best is None or hit.time<best.time: best=hit
    return best


def solve(rule,tile,defects=None,start=(0,0),heading=0,clauses=()):
    """Safe end-to-end entry point; result and query always share their input."""
    defects=dict(defects or {})
    result=decide(rule,tile,defects,start,heading)
    return result,first_hit(result,rule,tile,defects,clauses)
