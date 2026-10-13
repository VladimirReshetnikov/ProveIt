"""Validated synchronized nonnegative-port model and complete local rays."""
from dataclasses import dataclass
from itertools import combinations
from .exact import Q, matrix, dot, nullspace, primitive


class ResourceLimit(RuntimeError):
    """Incomplete computation; callers must not interpret this as a negative."""


@dataclass(frozen=True)
class Block:
    n: int
    equations: tuple
    ports: tuple
    conflicts: tuple = ()

    def __post_init__(self):
        if type(self.n) is not int or self.n < 1:
            raise ValueError('positive number of coordinates required')
        object.__setattr__(self,'equations',matrix(self.equations,self.n))
        object.__setattr__(self,'ports',matrix(self.ports,self.n))
        if not self.ports or any(v<0 for r in self.ports for v in r):
            raise ValueError('at least one entrywise nonnegative port row required')
        pairs=[]
        for p in self.conflicts:
            if len(p)!=2 or any(type(i) is not int or not 0<=i<self.n for i in p) or p[0]==p[1]:
                raise ValueError('invalid conflict pair')
            pairs.append(tuple(sorted(p)))
        object.__setattr__(self,'conflicts',tuple(sorted(set(pairs))))

    @property
    def d(self):
        return len(self.ports)

    def compatible_support(self, support):
        s=set(support)
        return not any(a in s and b in s for a,b in self.conflicts)

    def image(self, vector):
        return tuple(dot(row,vector) for row in self.ports)


def enumerate_rays(block, *, max_supports=None, check=lambda:None):
    """Every admissible full-cone extreme ray, with primitive integer scaling.

    Exhaustive support enumeration is intentionally simple and has a proved
    2**n polynomial-bit bound. No assumption on genericity or full row rank.
    """
    out=[]; visited=0
    for k in range(1,block.n+1):
        for s in combinations(range(block.n),k):
            check(); visited+=1
            if max_supports is not None and visited>max_supports:
                raise ResourceLimit('local support budget exhausted')
            if not block.compatible_support(s):
                continue
            basis=nullspace([tuple(row[j] for j in s) for row in block.equations],k)
            if len(basis)!=1:
                continue
            v=basis[0]
            if all(x<0 for x in v):
                v=tuple(-x for x in v)
            if not all(x>0 for x in v):
                continue
            full=[Q(0)]*block.n
            for j,x in zip(s,v): full[j]=x
            out.append(primitive(full))
    return tuple(out)


def enumerate_rays_by_zeros(block, *, max_supports=None, check=lambda:None):
    """Complete alternative with binom(n,h-1) candidates, h = nullity(A).

    The budget parameter counts candidate zero sets in this method. This is
    useful for long blocks with low algebraic nullity, not only small blocks.
    """
    h=len(nullspace(block.equations,block.n))
    if not h:return ()
    out=set();visited=0
    for zeros in combinations(range(block.n),h-1):
        check();visited+=1
        if max_supports is not None and visited>max_supports:
            raise ResourceLimit('local zero-set budget exhausted')
        z=set(zeros);s=tuple(j for j in range(block.n) if j not in z)
        basis=nullspace([tuple(row[j] for j in s) for row in block.equations],len(s))
        if len(basis)!=1:continue
        v=basis[0]
        if all(a<=0 for a in v):v=tuple(-a for a in v)
        if any(a<0 for a in v):continue
        full=[Q(0)]*block.n
        for j,a in zip(s,v):full[j]=a
        support=tuple(j for j,a in enumerate(full) if a)
        if block.compatible_support(support):out.add(primitive(full))
    return tuple(sorted(out))
