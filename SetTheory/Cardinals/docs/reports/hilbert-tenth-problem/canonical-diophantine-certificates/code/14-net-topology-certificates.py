#!/usr/bin/env python3
"""Exact sparse quadratic systems for loop-sensitive gluing and capped RAM logs.

All equations are over N = {0,1,...}. Polynomial export uses monomials as
sorted lists of variable names, with repetition indicating exponents.
This implements the two arithmetic kernels, not the full IC trace assembler.
No third-party dependencies.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
import json
from pathlib import Path
from typing import Mapping, Sequence

@dataclass
class Poly:
    terms: dict[tuple[str, ...], int]
    @staticmethod
    def const(n: int) -> 'Poly':
        return Poly({(): n} if n else {})
    @staticmethod
    def var(s: str) -> 'Poly':
        return Poly({(s,): 1})
    def __add__(self, other: 'Poly | int') -> 'Poly':
        other = other if isinstance(other, Poly) else Poly.const(other)
        d = self.terms.copy()
        for k, v in other.terms.items():
            d[k] = d.get(k, 0) + v
            if d[k] == 0: del d[k]
        return Poly(d)
    __radd__ = __add__
    def __neg__(self) -> 'Poly':
        return Poly({k: -v for k, v in self.terms.items()})
    def __sub__(self, other: 'Poly | int') -> 'Poly':
        return self + (-other if isinstance(other, Poly) else -int(other))
    def __rsub__(self, other: int) -> 'Poly':
        return Poly.const(other) - self
    def __mul__(self, other: 'Poly | int') -> 'Poly':
        other = other if isinstance(other, Poly) else Poly.const(other)
        d: dict[tuple[str, ...], int] = {}
        for x, a in self.terms.items():
            for y, b in other.terms.items():
                z = tuple(sorted(x+y)); d[z] = d.get(z, 0)+a*b
        return Poly({k: v for k, v in d.items() if v})
    __rmul__ = __mul__
    def evaluate(self, env: Mapping[str, int]) -> int:
        total = 0
        for m, c in self.terms.items():
            for v in m: c *= env[v]
            total += c
        return total
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)
    def serial(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items(), key=lambda z: (len(z[0]), z[0]))]

class System:
    def __init__(self):
        self.sources: list[str] = []
        self.aux: list[str] = []
        self.residuals: list[Poly] = []
    def variable(self, name: str, source: bool = False) -> Poly:
        if name in self.sources or name in self.aux: raise ValueError(name)
        (self.sources if source else self.aux).append(name)
        return Poly.var(name)
    def equation(self, p: Poly):
        if p.degree() > 2: raise ValueError("Not quadratic")
        self.residuals.append(p)
    def accepts(self, env: Mapping[str, int]) -> bool:
        names = self.sources+self.aux
        return all(type(env.get(n)) is int and env[n] >= 0 for n in names) and all(
            p.evaluate(env) == 0 for p in self.residuals)
    def export(self, path: Path, env: Mapping[str, int], metadata: dict):
        p = sum((r*r for r in self.residuals), Poly.const(0))
        obj = dict(metadata=metadata, domain="nonnegative integers",
                   source_variables=self.sources, auxiliary_variables=self.aux,
                   equations=[r.serial() for r in self.residuals],
                   quartic=p.serial(), degree=p.degree(),
                   witness=dict(env), witness_accepted=self.accepts(env))
        path.write_text(json.dumps(obj, indent=2)+"\n")
        return {"source_variables": len(self.sources), "auxiliaries": len(self.aux),
                "equations": len(self.residuals), "degree": p.degree(),
                "expanded_monomials": len(p.terms)}

EDGES = list(combinations(range(4), 2))
PERFECT = [frozenset(((0,1),(2,3))), frozenset(((0,2),(1,3))),
           frozenset(((0,3),(1,2)))]
JDELTA, JGAMMA = PERFECT[1], PERFECT[2]
def ename(i: int, j: int) -> str:
    return f"{min(i,j)}{max(i,j)}"
def loop_system(J=frozenset(JDELTA)) -> System:
    if J not in PERFECT: raise ValueError("Expected a perfect matching")
    s = System()
    m = {e: s.variable('m'+ename(*e), True) for e in EDGES}
    ext = [s.variable(f'e{i}') for i in range(4)]
    h = {e: s.variable('h'+ename(*e)) for e in EDGES}
    g = {e: s.variable('g'+ename(*e)) for e in EDGES}
    c = s.variable('cycles')
    for e in EDGES: s.equation(m[e]*(m[e]-1))
    for i in range(4):
        s.equation(ext[i]+sum((m[e] for e in EDGES if i in e), Poly.const(0))-1)
    jmap = {i: j for a,b in J for i,j in ((a,b),(b,a))}
    for i,j in EDGES:
        s.equation(h[(i,j)]-ext[i]*ext[j])
        factor = 1 if (i,j) in J else m[tuple(sorted((jmap[i],jmap[j])))]
        s.equation(g[(i,j)]-h[(i,j)]*factor)
    cyc = sum((m[e] for e in J), Poly.const(0))
    for K in PERFECT:
        if K != J:
            a,b = sorted(K); cyc += m[a]*m[b]
    s.equation(c-cyc)
    assert len(s.aux)==17 and len(s.residuals)==23
    return s

def loop_witness(M: set[tuple[int,int]], J=JDELTA) -> dict[str,int]:
    if J not in PERFECT or any(e not in EDGES for e in M):
        raise ValueError("Invalid boundary matching")
    if any(sum(i in e for e in M)>1 for i in range(4)):
        raise ValueError("Not a partial matching")
    out = {'m'+ename(*e): int(e in M) for e in EDGES}
    ext = [1-sum(i in e for e in M) for i in range(4)]
    out.update({f'e{i}': ext[i] for i in range(4)})
    jm = {i: j for a,b in J for i,j in ((a,b),(b,a))}
    for i,j in EDGES:
        h = ext[i]*ext[j]
        out['h'+ename(i,j)] = h
        out['g'+ename(i,j)] = h*(1 if (i,j) in J else int(tuple(sorted((jm[i],jm[j]))) in M))
    out['cycles'] = len(M.intersection(J))+sum(int(K.issubset(M)) for K in PERFECT if K!=J)
    return out

def memory_system(L: int, A: int, V: int) -> System:
    """Generate exactly 17L-4 auxiliary variables and quadratic residuals."""
    if any(type(n) is not int or n<1 for n in (L,A,V)): raise ValueError('positive caps required')
    S = System(); M = 2*A*L*V
    src = []
    for i in range(L):
        a,w,v = [S.variable(f'{x}{i}', True) for x in ('a','w','v')]
        src.append((a,w,v))
    rows = [tuple(S.variable(f'{x}{j}') for x in ('sa','st','sw','sv')) for j in range(L)]
    for i,(a,w,v) in enumerate(src):
        S.equation(a+S.variable(f'ba{i}')-(A-1))
        S.equation(v+S.variable(f'bv{i}')-(V-1))
        S.equation(w*(w-1))
    for j,(a,t,w,v) in enumerate(rows):
        for x,bound,nm in ((a,A,'bsa'),(t,L,'bst'),(v,V,'bsv')):
            S.equation(x+S.variable(f'{nm}{j}')-(bound-1))
        S.equation(w*(w-1))
    q = Poly.const(1)
    for i in range(L):
        nq = S.variable(f'q{i}'); S.equation(nq-(M+1)*q); q=nq
    B=q
    R=F=Poly.const(1)
    for i in range(L):
        a,w,v=src[i]; aa,t,ww,vv=rows[i]
        x=a+A*i+A*L*w+2*A*L*v
        y=aa+A*t+A*L*ww+2*A*L*vv
        nr=S.variable(f'R{i}'); nf=S.variable(f'F{i}')
        S.equation(nr-R*(B+x)); S.equation(nf-F*(B+y)); R,F=nr,nf
    S.equation(R-F)
    after=Poly.const(0)
    for j,(a,t,w,v) in enumerate(rows):
        before=Poly.const(0)
        if j:
            aa,tt,_,_=rows[j-1]
            gap=S.variable(f'gap{j}')
            S.equation(L*a+t-L*aa-tt-1-gap)
            bit=S.variable(f'new{j}'); h=S.variable(f'jump{j}')
            S.equation(bit*(bit-1)); S.equation(a-aa-bit*(1+h))
            S.equation((1-bit)*h)
            before=S.variable(f'pre{j}'); S.equation(before-(1-bit)*after)
        S.equation((1-w)*(v-before))
        z=S.variable(f'post{j}'); S.equation(z-w*v-(1-w)*before); after=z
    assert len(S.aux)==17*L-4, (len(S.aux),L)
    assert len(S.residuals)==17*L-4, (len(S.residuals),L)
    return S

def memory_witness(log: Sequence[tuple[int,int,int]], A: int, V: int) -> dict[str,int]:
    L=len(log)
    if not L: raise ValueError('nonempty log required')
    if any(type(x) is not int for row in log for x in row): raise TypeError('integer rows required')
    if any(not (0<=a<A and w in (0,1) and 0<=v<V) for a,w,v in log):
        raise ValueError('row outside caps')
    rows=sorted((a,i,w,v) for i,(a,w,v) in enumerate(log))
    E={}
    for i,(a,w,v) in enumerate(log):
        E.update({f'a{i}':a,f'w{i}':w,f'v{i}':v,f'ba{i}':A-1-a,f'bv{i}':V-1-v})
    for j,(a,t,w,v) in enumerate(rows):
        E.update({f'sa{j}':a,f'st{j}':t,f'sw{j}':w,f'sv{j}':v,
                  f'bsa{j}':A-1-a,f'bst{j}':L-1-t,f'bsv{j}':V-1-v})
    M=2*A*L*V; q=1
    for i in range(L): q*=M+1; E[f'q{i}']=q
    B=q; R=F=1
    for i,((a,w,v),(aa,t,ww,vv)) in enumerate(zip(log,rows)):
        R*=B+a+A*i+A*L*w+2*A*L*v
        F*=B+aa+A*t+A*L*ww+2*A*L*vv
        E[f'R{i}']=R; E[f'F{i}']=F
    after=0
    for j,(a,t,w,v) in enumerate(rows):
        before=0
        if j:
            aa,tt,_,_=rows[j-1]; bit=int(a!=aa)
            E[f'gap{j}']=L*a+t-L*aa-tt-1
            E[f'new{j}']=bit; E[f'jump{j}']=a-aa-1 if bit else 0
            before=(1-bit)*after; E[f'pre{j}']=before
        after=v if w else before; E[f'post{j}']=after
    return E

def valid_memory_log(log: Sequence[tuple[int,int,int]]) -> bool:
    mem={}
    for a,w,v in log:
        if w: mem[a]=v
        elif mem.get(a,0)!=v: return False
    return True
