#!/usr/bin/env python3
"""Exact priority-sensitive block certificates over natural numbers.

Standard library only, Python >= 3.10.  The compiler emits an explicit sum of
squares of quadratic residuals, not an invocation of MRDP.  The word and its
length are compile-time data; the program entries, initial counters, repetition
count and requested endpoint are free natural-number inputs.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Mapping, Sequence
import argparse
import json
from pathlib import Path

@dataclass(frozen=True)
class Poly:
    terms: dict[tuple[int, ...], int]
    @staticmethod
    def const(v: int) -> 'Poly':
        return Poly({(): v} if v else {})
    @staticmethod
    def var(i: int) -> 'Poly':
        return Poly({(i,): 1})
    def __add__(self, other: int | 'Poly') -> 'Poly':
        other = as_poly(other)
        d = self.terms.copy()
        for m, c in other.terms.items():
            d[m] = d.get(m, 0) + c
            if not d[m]: del d[m]
        return Poly(d)
    __radd__ = __add__
    def __neg__(self) -> 'Poly':
        return Poly({m: -c for m, c in self.terms.items()})
    def __sub__(self, other: int | 'Poly') -> 'Poly':
        return self + -as_poly(other)
    def __rsub__(self, other: int | 'Poly') -> 'Poly':
        return as_poly(other) + -self
    def __mul__(self, other: int | 'Poly') -> 'Poly':
        other = as_poly(other)
        d: dict[tuple[int, ...], int] = {}
        for a, ac in self.terms.items():
            for b, bc in other.terms.items():
                m = tuple(sorted(a + b))
                d[m] = d.get(m, 0) + ac * bc
        return Poly({m: c for m, c in d.items() if c})
    __rmul__ = __mul__
    def evaluate(self, vals: Sequence[int]) -> int:
        total = 0
        for mon, coeff in self.terms.items():
            t = coeff
            for i in mon: t *= vals[i]
            total += t
        return total
    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)
    def text(self, names: Sequence[str]) -> str:
        if not self.terms: return '0'
        parts = []
        for m, c in sorted(self.terms.items(), key=lambda kv: (len(kv[0]), kv[0])):
            body = '*'.join(names[i] for i in m)
            parts.append(str(c) + ('*' + body if body else ''))
        return '(' + ' + '.join(parts).replace('+ -', '- ') + ')'
    def json_terms(self) -> list[dict]:
        return [{'coefficient': c, 'variables': list(m)}
                for m, c in sorted(self.terms.items())]

def as_poly(x: int | Poly) -> Poly:
    return x if isinstance(x, Poly) else Poly.const(x)

class Circuit:
    def __init__(self) -> None:
        self.names: list[str] = []
        self.inputs: dict[str, int] = {}
        self.operations: list[tuple[str, tuple[Poly, ...], tuple[int, ...]]] = []
        self.residuals: list[Poly] = []
        self.obligations: list[Poly] = []
        self.accept: Poly | None = None
    def _new(self, name: str | None = None) -> tuple[Poly, int]:
        i = len(self.names)
        self.names.append(name if name is not None else f'z{i}')
        return Poly.var(i), i
    def input(self, name: str) -> Poly:
        if name in self.inputs: raise ValueError('Duplicate input: ' + name)
        p, i = self._new(name)
        self.inputs[name] = i
        return p
    def constrain(self, p: int | Poly, obligation: bool = False) -> None:
        p = as_poly(p)
        if p.degree > 2: raise ValueError('Residual degree exceeds two')
        (self.obligations if obligation else self.residuals).append(p)
    def assign(self, expr: int | Poly) -> Poly:
        expr = as_poly(expr)
        p, i = self._new()
        self.operations.append(('assign', (expr,), (i,)))
        self.constrain(p - expr)
        return p
    def lt(self, u: int | Poly, v: int | Poly) -> tuple[Poly, Poly]:
        """b=[u<v], and s=v-u-1 if b=1, otherwise s=u-v."""
        u, v = as_poly(u), as_poly(v)
        b, bi = self._new(); s, si = self._new()
        self.operations.append(('lt', (u, v), (bi, si)))
        self.constrain(b*(b-1))
        self.constrain(b*(v-u-1-s))
        self.constrain((1-b)*(u-v-s))
        return b, s
    def div(self, a: int | Poly, d: int | Poly) -> Poly:
        """Unique Euclidean quotient; construction must ensure d>=1."""
        a, d = as_poly(a), as_poly(d)
        q, qi = self._new(); r, ri = self._new(); t, ti = self._new()
        self.operations.append(('div', (a,d), (qi,ri,ti)))
        self.constrain(a-d*q-r)
        self.constrain(d-r-1-t)
        return q
    def minimum(self, u: int | Poly, v: int | Poly) -> Poly:
        u, v = as_poly(u), as_poly(v)
        b, _ = self.lt(u,v)
        return self.assign(v-b*(v-u))
    def maximum(self, u: int | Poly, v: int | Poly) -> Poly:
        u, v = as_poly(u), as_poly(v)
        b, _ = self.lt(u,v)
        return self.assign(u+b*(v-u))
    def witness(self, inputs: Mapping[str,int]) -> list[int]:
        if set(inputs) != set(self.inputs):
            missing, extra = set(self.inputs)-set(inputs), set(inputs)-set(self.inputs)
            raise ValueError(f'Input mismatch: missing={missing}, extra={extra}')
        vals = [0] * len(self.names)
        for name, i in self.inputs.items():
            v = inputs[name]
            if not isinstance(v, int) or isinstance(v, bool) or v < 0:
                raise ValueError(f'{name} must be a natural number')
            vals[i] = v
        for kind, args, outs in self.operations:
            av = [p.evaluate(vals) for p in args]
            if kind == 'assign': out = av
            elif kind == 'lt':
                u,v=av
                out = [int(u<v), v-u-1 if u<v else u-v]
            elif kind == 'div':
                a,d=av
                if a<0 or d<1: raise ArithmeticError(f'Invalid division {a}//{d}')
                q,r=divmod(a,d); out=[q,r,d-r-1]
            else: raise AssertionError(kind)
            if any(v<0 for v in out):
                raise ArithmeticError(f'Negative auxiliary at {kind}: {out}')
            for i,v in zip(outs,out): vals[i]=v
        return vals
    def value(self, vals: Sequence[int], include_obligations: bool = True) -> int:
        rs = self.residuals + (self.obligations if include_obligations else [])
        return sum(p.evaluate(vals)**2 for p in rs)
    def stats(self) -> dict:
        rs = self.residuals + self.obligations
        return {'free_inputs':len(self.inputs), 'auxiliary_variables':len(self.names)-len(self.inputs),
                'quadratic_residuals':len(rs), 'gate_residuals':len(self.residuals),
                'final_obligations':len(self.obligations),
                'maximum_residual_degree':max((p.degree for p in rs),default=0),
                'maximum_residual_support':max((len(p.terms) for p in rs),default=0),
                'maximum_residual_coefficient':max((abs(c) for p in rs for c in p.terms.values()),default=0),
                'sum_of_squares_degree_bound':2*max((p.degree for p in rs),default=0)}
    def export(self, path: Path) -> None:
        obj={'domain':'nonnegative integers','polynomial':'sum of squares of residuals',
             'variable_order':self.names,'free_inputs':list(self.inputs),
             'residuals':[p.json_terms() for p in self.residuals+self.obligations],
             'statistics':self.stats()}
        path.write_text(json.dumps(obj,indent=2)+'\n')

@dataclass
class Slopes:
    positive: Poly
    negative: Poly
    eplus: Poly
    eminus: Poly
    ezero: Poly
    dplus: Poly
    dminus: Poly
    grow_k: Poly
    flat_k: Poly

def interval(c: Circuit, u: Poly, v: Poly, sl: Slopes, k: Poly) -> tuple[Poly,Poly]:
    """All h in [0,k) with u-v+h*(positive-negative)>=0."""
    bad, gap = c.lt(u,v)
    deficit = c.assign(bad*(gap+1))
    surplus = c.assign((1-bad)*gap)
    ceil_numerator = c.assign(deficit+sl.dplus-1)
    ceiling = c.div(ceil_numerator,sl.dplus)
    lower = c.assign(sl.eplus*c.minimum(k,ceiling))
    floor = c.div(surplus,sl.dminus)
    upper_down = c.assign((1-bad)*c.minimum(k,floor+1))
    down = c.assign(sl.eminus*upper_down)
    flat = c.assign(sl.flat_k*(1-bad))
    upper = c.assign(sl.grow_k+down+flat)
    return lower,upper

def core(c: Circuit,A:list[list[Poly]],B:list[list[Poly]],x:list[Poly],
         k:Poly,word:Sequence[int]) -> tuple[Poly,list[Poly],list[Poly]]:
    d=len(x); ell=len(word)
    pa=[[Poly.const(0) for _ in range(d)]]
    pb=[[Poly.const(0) for _ in range(d)]]
    for j in word:
        pa.append([c.assign(pa[-1][p]+A[j][p]) for p in range(d)])
        pb.append([c.assign(pb[-1][p]+B[j][p]) for p in range(d)])
    slopes=[]
    for p in range(d):
        minus,gap=c.lt(pa[-1][p],pb[-1][p])
        plus,_=c.lt(pb[-1][p],pa[-1][p])
        pos=c.assign((1-minus)*gap)
        neg=c.assign(minus*(gap+1))
        dp=c.assign(pos+1-plus); dm=c.assign(neg+1-minus)
        zero=1-plus-minus
        slopes.append(Slopes(pos,neg,plus,minus,zero,dp,dm,
                             c.assign(plus*k),c.assign(zero*k)))
    accept=Poly.const(1)
    for r,j in enumerate(word):
        us=[c.assign(x[p]+pa[r][p]) for p in range(d)]
        for i in range(j+1):
            low,high=Poly.const(0),k
            for p in range(d):
                v=c.assign(B[i][p]+pb[r][p])
                lo,hi=interval(c,us[p],v,slopes[p],k)
                low=c.maximum(low,lo); high=c.minimum(high,hi)
            if i<j:
                nonempty,_=c.lt(low,high)
                check=1-nonempty
            else:
                low_zero,_=c.lt(low,1)
                high_short,_=c.lt(high,k)
                check=c.assign(low_zero*(1-high_short))
            accept=c.assign(accept*check)
    return accept,pa[-1],pb[-1]

def compile_block(m:int,d:int,word:Sequence[int],*,endpoint:bool=True,
                  reject:bool=False,maximal:bool=False,reduced:bool=False) -> Circuit:
    if m<1 or d<1 or not word or any(not 0<=j<m for j in word):
        raise ValueError('Require positive m,d and a nonempty in-range word')
    if maximal and reject: raise ValueError('maximal and reject are incompatible')
    c=Circuit()
    A=[[c.input(f'A_{i}_{p}') for p in range(d)] for i in range(m)]
    B=[[c.input(f'B_{i}_{p}') for p in range(d)] for i in range(m)]
    x=[c.input(f'x_{p}') for p in range(d)]
    k=c.input('k')
    y=[c.input(f'y_{p}') for p in range(d)] if endpoint else []
    accept,P,Q=core(c,A,B,x,k,word)
    c.accept=accept
    c.constrain(accept-(0 if reject else 1),obligation=True)
    if maximal:
        next_accept,_,_=core(c,A,B,x,k+1,word)
        c.constrain(next_accept,obligation=True)
    if endpoint:
        for p in range(d):
            kp=c.assign(k*P[p]); kq=c.assign(k*Q[p])
            c.constrain(x[p]+kp-y[p]-kq,obligation=True)
    if reduced:
        for i in range(m):
            for p in range(d): c.constrain(A[i][p]*B[i][p],obligation=True)
    return c

def as_inputs(A:Sequence[Sequence[int]],B:Sequence[Sequence[int]],x:Sequence[int],
              k:int,y:Sequence[int]|None=None) -> dict[str,int]:
    vals={f'A_{i}_{p}':v for i,row in enumerate(A) for p,v in enumerate(row)}
    vals.update({f'B_{i}_{p}':v for i,row in enumerate(B) for p,v in enumerate(row)})
    vals.update({f'x_{p}':v for p,v in enumerate(x)}); vals['k']=k
    if y is not None: vals.update({f'y_{p}':v for p,v in enumerate(y)})
    return vals

def step(A:Sequence[Sequence[int]],B:Sequence[Sequence[int]],x:Sequence[int]):
    for i,(a,b) in enumerate(zip(A,B)):
        if all(v>=g for v,g in zip(x,b)):
            return i,tuple(v-g+t for v,g,t in zip(x,b,a))
    return None

def unroll(A,B,x,word,k):
    x=tuple(x)
    for _ in range(k):
        for j in word:
            st=step(A,B,x)
            if st is None or st[0]!=j: return False,x
            x=st[1]
    return True,x

def affine_interval(a:int,s:int,k:int)->tuple[int,int]:
    if k<0: raise ValueError('k must be nonnegative')
    if s>0: return min(k,max(0,(-a+s-1)//s)),k
    if s<0: return 0,min(k,a//(-s)+1) if a>=0 else 0
    return (0,k) if a>=0 else (0,0)

def block_valid(A,B,x,word,k)->bool:
    d=len(x)
    delta=[sum(A[j][p]-B[j][p] for j in word) for p in range(d)]
    base=list(x)
    for j in word:
        for i in range(j+1):
            lo,hi=0,k
            for p in range(d):
                l,u=affine_interval(base[p]-B[i][p],delta[p],k)
                lo,hi=max(lo,l),min(hi,u)
            if (i<j and lo<hi) or (i==j and (lo!=0 or hi!=k)): return False
        base=[base[p]+A[j][p]-B[j][p] for p in range(d)]
    return True

def infinite_word(A,B,x,word)->bool:
    d=len(x)
    delta=[sum(A[j][p]-B[j][p] for j in word) for p in range(d)]
    if any(v<0 for v in delta): return False
    base=list(x)
    for j in word:
        if any(base[p]<B[j][p] for p in range(d)): return False
        for i in range(j):
            if not any(delta[p]==0 and base[p]<B[i][p] for p in range(d)):
                return False
        base=[base[p]+A[j][p]-B[j][p] for p in range(d)]
    return True

def maximal_blocks(A,B,x,word)->int|None:
    """None means infinitely many. No unrolling; binary search is exact."""
    if infinite_word(A,B,x,word): return None
    lo,hi=0,1
    while block_valid(A,B,x,word,hi): lo,hi=hi,hi*2
    while lo+1<hi:
        mid=(lo+hi)//2
        if block_valid(A,B,x,word,mid): lo=mid
        else: hi=mid
    return lo

def repetition_capacity(A,B,word):
    """Return (capacity, least_one_block_seed, drift).

    Capacity None means arbitrarily many copies from suitably chosen seeds.
    It is NOT the same as infinite repetition from one seed.
    """
    d=len(A[0])
    base=[0]*d; prefixes=[]; least=[0]*d
    for j in word:
        prefixes.append(base[:])
        least=[max(least[p],B[j][p]-base[p]) for p in range(d)]
        base=[base[p]+A[j][p]-B[j][p] for p in range(d)]
    delta=base
    capacity=None
    for r,j in enumerate(word):
        for i in range(j):
            c=[least[p]+prefixes[r][p]-B[i][p] for p in range(d)]
            if any(delta[p]==0 and c[p]<0 for p in range(d)):
                continue
            left=right=0
            for p in range(d):
                deficit=max(0,-c[p])
                if delta[p]>0:
                    left=max(left,(deficit+delta[p]-1)//delta[p])
                elif delta[p]<0:
                    n=-delta[p]
                    right=max(right,(deficit+n-1)//n)
            cap=left+right
            capacity=cap if capacity is None else min(capacity,cap)
    return capacity,least,delta

def least_seed_for_repetitions(A,B,word,k):
    if k<0: raise ValueError('k must be nonnegative')
    if k==0: return [0]*len(A[0])
    _,least,delta=repetition_capacity(A,B,word)
    return [a+(k-1)*max(0,-s) for a,s in zip(least,delta)]

def factor(n:int)->dict[int,int]:
    if n<1: raise ValueError('positive integers required')
    result={}; p=2
    while p*p<=n:
        while n%p==0: result[p]=result.get(p,0)+1; n//=p
        p=3 if p==2 else p+2
    if n>1: result[n]=result.get(n,0)+1
    return result

def from_fractions(fracs:Sequence[tuple[int,int]]):
    reduced=[Fraction(a,b) for a,b in fracs]
    if any(f<=0 for f in reduced): raise ValueError('positive fractions required')
    nums=[factor(f.numerator) for f in reduced]
    dens=[factor(f.denominator) for f in reduced]
    primes=sorted(set().union(*(set(f) for f in nums+dens)))
    if not primes: primes=[2]  # a harmless zero counter for the all-1 program
    A=[[f.get(p,0) for p in primes] for f in nums]
    B=[[f.get(p,0) for p in primes] for f in dens]
    return primes,A,B

def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export',type=Path,default=Path('certificate.json'))
    args=parser.parse_args()
    # Program (1/72,3/2), word consisting of the second fraction.
    primes,A,B=from_fractions([(1,72),(3,2)])
    c=compile_block(2,2,[1],endpoint=True)
    args.export.parent.mkdir(parents=True,exist_ok=True); c.export(args.export)
    print(json.dumps({'prime_order':primes,'statistics':c.stats(),'path':str(args.export)},indent=2))

if __name__=='__main__': main()
