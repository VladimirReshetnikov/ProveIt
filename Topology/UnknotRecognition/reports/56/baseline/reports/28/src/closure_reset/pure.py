"""Whole-direct-summand certification. No interval-product ranks are needed."""
from __future__ import annotations
from dataclasses import dataclass, asdict
from .binary import rank
from .dots import parity, validate

@dataclass(frozen=True)
class PureData:
    vertices: tuple[int,...]
    matching: int
    theta: int
    dimensions: tuple[int,...]
    arrows: tuple[tuple[int,...],...]
    beta: int
    sigma: int
    has_edge: bool
    lower_bound: int
    def as_dict(self): return asdict(self)

def components(scan):
    live={i for i,m in enumerate(scan.mid) if m is not None}
    while live:
        start=min(live); live.remove(start); todo=[start]; group=[]
        while todo:
            v=todo.pop(); group.append(v)
            neighbors=set(scan.out[v]) | set(scan.inc[v])
            for w in sorted(neighbors):
                if w in live: live.remove(w); todo.append(w)
        yield tuple(sorted(group))

def certify(scan, group):
    group=tuple(group)
    if not group: raise ValueError('empty summand')
    members=set(group)
    if len(members)!=len(group) or any(v<0 or v>=len(scan.mid) or scan.mid[v] is None for v in group):
        raise ValueError('invalid live vertex set')
    m=scan.mid[group[0]]
    for v in group:
        if not set(scan.out[v]).issubset(members) or not set(scan.inc[v]).issubset(members):
            raise ValueError('proposed block has external differential attachments')
    if any(scan.mid[v]!=m for v in group): return None
    p=len(scan.algebra.pairs[m])
    if p==0: return None  # Empty boundary needs the scalar terminal rule.
    theta=None
    for v in group:
        for w,value in scan.out[v].items():
            if not value or value&1: return None
            validate(value,p,radical=True)
            if scan.deg[w]!=scan.deg[v]+1: raise ValueError('differential degree mismatch')
            if theta is None: theta=value
            elif theta!=value: return None
    first=min(scan.deg[v] for v in group); last=max(scan.deg[v] for v in group)
    layers=[[] for _ in range(last-first+1)]
    for v in group: layers[scan.deg[v]-first].append(v)
    dims=tuple(len(row) for row in layers); arrows=[]
    for h,row in enumerate(layers[:-1]):
        ix={v:i for i,v in enumerate(layers[h+1])}
        arrows.append(tuple(sum(1<<ix[w] for w in scan.out[v]) for v in row))
    ranks=tuple(rank(a) for a in arrows); beta=sum(dims)-sum(ranks)
    if beta<1: raise ArithmeticError('nonempty finite quiver has no intervals')
    theta=theta or 0; sigma=parity(theta); edge=any(ranks)
    # Strong lower bound uses coherent dot sliding for knot completions and
    # r_l >= r_1 plus >=4 nonempty two-component homology otherwise.
    lower=2*beta if sigma else 2*min(sum(dims),2*beta)
    return PureData(group,m,theta,dims,tuple(arrows),beta,sigma,edge,lower)

def inspect(scan):
    """Return whole components and an additive certified rank lower bound."""
    groups=list(components(scan)); data=[certify(scan,g) for g in groups]
    lower=sum(d.lower_bound for d in data if d is not None)
    return groups,data,lower
