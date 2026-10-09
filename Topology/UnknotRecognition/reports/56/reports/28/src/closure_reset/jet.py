"""Knot-context first-jet certificate for radical single-matching summands.
Higher dot coefficients do not affect completed total rank when the matching
closed by the actual suffix is a knot. This premise is checked by the driver.
No claim is made for a multi-component closure in this interface.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from .binary import rank
from .dots import parity, validate

@dataclass(frozen=True)
class JetData:
    vertices: tuple[int,...]
    matching: int
    dimensions: tuple[int,...]
    arrows: tuple[tuple[int,...],...]
    kappa: int
    has_edge: bool
    def as_dict(self): return asdict(self)

def certify_jet(scan,group):
    """Read a WHOLE radical single-matching component of a valid chain complex.
    Validity d^2=0 is inherited from the exact scanner, not guessed from its
    first jet. This function verifies the shape and all boundary attachments.
    """
    group=tuple(group); members=set(group)
    if not group or len(members)!=len(group): raise ValueError('invalid vertex set')
    if any(type(v) is not int or v<0 or v>=len(scan.mid) or scan.mid[v] is None for v in group):
        raise ValueError('invalid live vertex')
    m=scan.mid[group[0]]
    for v in group:
        if not set(scan.out[v]).issubset(members) or not set(scan.inc[v]).issubset(members):
            raise ValueError('proposed jet block has external differential attachments')
    if any(scan.mid[v]!=m for v in group): return None
    p=len(scan.algebra.pairs[m])
    if not p: return None
    for v in group:
        for w,f in scan.out[v].items():
            if f&1: return None # Caller may first perform exact unit cancellation.
            validate(f,p,radical=True)
            if scan.deg[w]!=scan.deg[v]+1: raise ValueError('differential degree mismatch')
    first=min(scan.deg[v] for v in group); last=max(scan.deg[v] for v in group)
    layers=[[] for _ in range(last-first+1)]
    for v in group: layers[scan.deg[v]-first].append(v)
    dims=tuple(map(len,layers)); arrows=[]
    for h,row in enumerate(layers[:-1]):
        ix={v:i for i,v in enumerate(layers[h+1])}
        arrows.append(tuple(sum(1<<ix[w] for w,f in scan.out[v].items() if parity(f)) for v in row))
    kappa=sum(dims)-sum(rank(a) for a in arrows)
    if kappa<1: raise ArithmeticError('nonempty bounded radical jet has no survivor')
    return JetData(group,m,dims,tuple(arrows),kappa,any(scan.out[v] for v in group))

def first_jet_survivors(scalar_columns, linear_columns):
    """Return kappa = dim H(A) - rank(B_*), for A^2=0 and AB+BA=0.

    A and B are equally sized square column-packed binary matrices. In the
    theorem they both raise the bounded homological degree by one. This
    helper checks the matrix identities but cannot infer an omitted grading.
    It is an exact algebraic computation, not by itself a knot certificate.
    """
    from .binary import apply, compose
    A=tuple(scalar_columns); B=tuple(linear_columns); n=len(A)
    if len(B)!=n or any(type(c) is not int or c<0 or c.bit_length()>n for c in A+B):
        raise ValueError('first-jet matrices must be square and equally sized')
    if any(compose(A,A)): raise ValueError('scalar differential does not square to zero')
    if any(x^y for x,y in zip(compose(A,B),compose(B,A))):
        raise ValueError('linear part does not commute with scalar differential')
    pivots={}; kernel=[]
    for j,column in enumerate(A):
        v=column; relation=1<<j
        while v:
            k=v.bit_length()-1
            if k not in pivots:
                pivots[k]=(v,relation); break
            p,q=pivots[k]; v^=p; relation^=q
        if not v: kernel.append(relation)
    rA=len(pivots); homology=n-2*rA
    image_rank=rank(list(A)+[apply(B,v) for v in kernel])-rA
    return dict(scalar_homology=homology,induced_linear_rank=image_rank,
                kappa=homology-image_rank)
