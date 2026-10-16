# Adapted from the pinned incoming zfc_tm_pure_subset_research.zip.
# Only equality-free closure() is used by the new tableau checker.
"""Equality-free first-order syntax and independent template measurements.

Only the Python standard library is required. This is an executable reference,
not a verified kernel. T and B are logical truth and falsity, not membership atoms.
"""
from __future__ import annotations
from math import isqrt
from typing import Any

Formula = tuple
T: Formula = ('T',)
B: Formula = ('B',)

def E(x: int, y: int) -> Formula: return ('E', x, y)
def Eq(x: int, y: int) -> Formula: return ('eq', x, y)
def I(a: Formula, b: Formula) -> Formula: return ('I', a, b)
def A(x: int, a: Formula) -> Formula: return ('A', x, a)
def N(a: Formula) -> Formula: return I(a, B)
def And(a: Formula, b: Formula) -> Formula: return N(I(a, N(b)))
def Or(a: Formula, b: Formula) -> Formula: return I(N(a), b)
def Iff(a: Formula, b: Formula) -> Formula: return And(I(a,b), I(b,a))
def Ex(x: int, a: Formula) -> Formula: return N(A(x, N(a)))
def All(xs: list[int], a: Formula) -> Formula:
    for x in reversed(xs): a = A(x, a)
    return a

def nat(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError('A label/code must be a nonnegative integer, not a Boolean')
    return x

def parse(obj: Any) -> Formula:
    if not isinstance(obj, (list,tuple)) or not obj:
        raise ValueError('Expected a nonempty formula array')
    tag = obj[0]
    if tag in ('T','B') and len(obj)==1: return (tag,)
    if tag=='E' and len(obj)==3: return E(nat(obj[1]),nat(obj[2]))
    if tag=='I' and len(obj)==3: return I(parse(obj[1]),parse(obj[2]))
    if tag=='A' and len(obj)==3: return A(nat(obj[1]),parse(obj[2]))
    raise ValueError('Unknown constructor or wrong arity; equality and holes are not executable')

def labels(f: Formula) -> set[int]:
    if f[0] in ('E','eq','H'): return set(f[1:])
    if f[0]=='I': return labels(f[1]) | labels(f[2])
    if f[0]=='A': return {f[1]} | labels(f[2])
    return set()

def free(f: Formula) -> set[int]:
    if f[0] in ('E','eq','H'): return set(f[1:])
    if f[0]=='I': return free(f[1]) | free(f[2])
    if f[0]=='A': return free(f[2]) - {f[1]}
    return set()

def rename_free(f: Formula, old: int, new: int) -> Formula:
    """Rename free occurrences. Used with a globally fresh new label."""
    if f[0] in ('E','eq','H'):
        return (f[0], *(new if x==old else x for x in f[1:]))
    if f[0]=='I': return I(rename_free(f[1],old,new),rename_free(f[2],old,new))
    if f[0]=='A':
        if f[1]==old: return f
        return A(f[1],rename_free(f[2],old,new))
    return f

def subst(f: Formula, env: dict[int,int]) -> Formula:
    """Simultaneous capture-avoiding substitution of free variable labels."""
    env={nat(k):nat(v) for k,v in env.items()}
    if f[0] in ('E','eq','H'): return (f[0],*(env.get(x,x) for x in f[1:]))
    if f[0]=='I': return I(subst(f[1],env),subst(f[2],env))
    if f[0]=='A':
        x,body=f[1],f[2]
        local={k:v for k,v in env.items() if k!=x and k in free(body)}
        if x in local.values():
            fresh=1+max(labels(body)|set(local)|set(local.values())|{x})
            body=rename_free(body,x,fresh)
            x=fresh
        return A(x,subst(body,local))
    return f

def alpha_key(f: Formula, bound: tuple[int,...]=()) -> tuple:
    def var(x: int) -> tuple:
        return ('bound',bound.index(x)) if x in bound else ('free',x)
    if f[0] in ('E','eq','H'): return (f[0],*(var(x) for x in f[1:]))
    if f[0]=='I': return ('I',alpha_key(f[1],bound),alpha_key(f[2],bound))
    if f[0]=='A': return ('A',alpha_key(f[2],(f[1],)+bound))
    return f

def Sub(x: int, y: int, z: int) -> Formula: return A(z,I(E(z,x),E(z,y)))

def congruence(style: str='directed') -> Formula:
    x,y,w,z=range(4)
    if style=='directed':
        return All([x,y,w],I(Sub(x,y,z),I(Sub(y,x,z),I(E(x,w),E(y,w)))))
    d=A(z,Iff(E(z,x),E(z,y)))
    if style=='old': return All([x,y],I(d,A(w,Iff(E(x,w),E(y,w)))))
    raise ValueError('Unknown congruence style')

def extensionality(style: str='directed') -> Formula:
    x,y,z=range(3)
    if style=='directed': return All([x,y],I(Sub(x,y,z),I(Sub(y,x,z),Eq(x,y))))
    if style=='old': return All([x,y],I(A(z,Iff(E(z,x),E(z,y))),Eq(x,y)))
    raise ValueError('Unknown extensionality style')

def closure(matrix: Formula, *, seed: str='subset', mixed: bool=False,
            curried: bool=True, close_parameters: bool=True) -> Formula:
    """Generate the schema; free matrix slots 0,1 are input/output.

    All wrapper variables are fresh above every matrix label. Parameters are
    universally closed, never confused with the schema's fresh seed variable.
    """
    m=1+max(labels(matrix)|{0,1})
    x,y,b,a,c,z=range(m,m+6)
    rho=subst(matrix,{0:x,1:y})
    bound=Sub(y,b,z)
    if mixed: bound=Or(E(y,b),bound)
    premise=A(x,Ex(b,A(y,I(rho,bound))))
    s=Sub(x,a,z) if seed=='subset' else Eq(x,a)
    if seed not in ('subset','point'): raise ValueError('Unknown seed')
    start=Or(s,E(x,c))
    step=I(start,I(rho,E(y,c))) if curried else I(And(start,rho),E(y,c))
    forward=All([x,y],step)
    purity=A(y,I(E(y,c),Ex(x,rho)))
    result=I(premise,A(a,Ex(c,And(forward,purity))))
    return All(sorted(free(matrix)-{0,1}),result) if close_parameters else result

def nodes(f: Formula) -> int:
    if f[0]=='I': return 1+nodes(f[1])+nodes(f[2])
    if f[0]=='A': return 1+nodes(f[2])
    return 1

def evaluate(f: Formula, mem: tuple[int,...], env: dict[int,int]) -> bool:
    """Finite semantics. mem[y] is a bit mask of the members of y."""
    op=f[0]
    if op=='T': return True
    if op=='B': return False
    if op=='E': return bool(mem[env[f[2]]] & (1<<env[f[1]]))
    if op=='eq': return env[f[1]]==env[f[2]]
    if op=='I': return not evaluate(f[1],mem,env) or evaluate(f[2],mem,env)
    if op=='A': return all(evaluate(f[2],mem,env|{f[1]:x}) for x in range(len(mem)))
    raise ValueError('Cannot evaluate a schema hole')

def pair(x: int,y: int) -> int:
    x,y=nat(x),nat(y)
    return (x+y)*(x+y+1)//2+y

def unpair(n: int) -> tuple[int,int]:
    n=nat(n); s=(isqrt(8*n+1)-1)//2
    y=n-s*(s+1)//2
    return s-y,y

def decode(n: int) -> Formula:
    """Total four-tag decoder. 0=True; 4k+1=False; 4k+3=membership.

    Positive implication and quantifier codes have strictly smaller children.
    Python's resource limits are not a mathematical termination certificate.
    """
    n=nat(n)
    if n==0: return T
    tag=n%4
    if tag==1: return B
    x,y=unpair(n//4)
    if tag==3: return E(x,y)
    if tag==2: return A(x,decode(y))
    return I(decode(x),decode(y))

def smart_imp(a: Formula,b: Formula) -> Formula:
    return T if a==T and b==T else I(a,b)

def normalize(f: Formula) -> Formula:
    if f[0]=='I': return smart_imp(normalize(f[1]),normalize(f[2]))
    if f[0]=='A': return A(f[1],normalize(f[2]))
    return f

def encode(f: Formula) -> int:
    if f==T: return 0
    if f==B: return 1
    if f[0]=='E': return 4*pair(f[1],f[2])+3
    if f[0]=='A': return 4*pair(f[1],encode(f[2]))+2
    if f[0]=='I': return 4*pair(encode(f[1]),encode(f[2]))
    raise ValueError('Only executable syntax is encodable')
