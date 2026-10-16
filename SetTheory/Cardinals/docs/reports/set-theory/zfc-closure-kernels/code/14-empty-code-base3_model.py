"""Exact total base-three syntax and a countermodel to the reduced calculus.

This is a Boolean algebra model of NUMERIC FORMULAS, not a membership model.
All quantifier operators are the identity.  It must not be confused with
first-order semantics, where bound variables range over a common domain.
"""
from functools import lru_cache
from math import isqrt

TOP = ('top',)

def natural(x):
    if type(x) is not int or x < 0:
        raise ValueError('expected a natural number')
    return x

def pair(a, b):
    natural(a); natural(b)
    s = a + b
    return s * (s + 1) // 2 + b

def unpair(n):
    natural(n)
    s = (isqrt(8*n + 1) - 1) // 2
    b = n - s*(s+1)//2
    return s-b, b

def imp(a,b): return 3*pair(a,b)
def rel(i,j): return 3*pair(i,j)+1
def all_(i,a): return 3*pair(i,a)+2

@lru_cache(maxsize=None)
def decode(n):
    natural(n)
    if n == 0:
        return TOP
    a,b=unpair(n//3)
    assert a < n and b < n
    if n%3 == 0: return ('imp',decode(a),decode(b))
    if n%3 == 1: return ('mem',a,b)
    return ('all',a,decode(b))

def encode(f):
    if f == TOP: return 0
    if f[0]=='mem': return rel(f[1],f[2])
    if f[0]=='imp': return imp(encode(f[1]),encode(f[2]))
    if f[0]=='all': return all_(f[1],encode(f[2]))
    raise ValueError(f)

def normalize(f):
    if f == TOP or f[0]=='mem': return f
    if f[0]=='all': return ('all',f[1],normalize(f[2]))
    if f[0]=='imp':
        a,b=normalize(f[1]),normalize(f[2])
        return TOP if a==TOP and b==TOP else ('imp',a,b)
    raise ValueError(f)

def labels(f):
    if f==TOP:return ()
    if f[0]=='mem':return (f[1],f[2])
    if f[0]=='imp':return labels(f[1])+labels(f[2])
    if f[0]=='all':return (f[1],)+labels(f[2])
    raise ValueError(f)

@lru_cache(maxsize=None)
def value(n):
    """A well-founded truth valuation; value(0)=True and value(1)=False."""
    natural(n)
    if n==0:return True
    a,b=unpair(n//3)
    assert a<n and b<n
    if n%3==0:return (not value(a)) or value(b)
    if n%3==1:return a==1 and value(b)
    return value(b)

@lru_cache(maxsize=None)
def value_star(n):
    """Symmetric obstruction: even explicit irreflexivity remains valid."""
    natural(n)
    if n==0:return True
    a,b=unpair(n//3)
    assert a<n and b<n
    if n%3==0:return (not value_star(a)) or value_star(b)
    if n%3==1:return a!=b and value_star(b)
    return value_star(b)

def evaluate_pattern(f, parameters, star=False):
    """Evaluate emitted constructor trees without constructing enormous codes."""
    truth=value_star if star else value
    if type(f) is int:return truth(f)
    if isinstance(f,str):return truth(parameters[f])
    kind,a,b=f
    def label(x):return parameters[x] if isinstance(x,str) else x
    if kind=='imp':return not evaluate_pattern(a,parameters,star) or evaluate_pattern(b,parameters,star)
    if kind=='rel':return ((label(a)!=label(b)) if star else (label(a)==1)) and truth(label(b))
    if kind=='all':return evaluate_pattern(b,parameters,star)
    raise ValueError(f'unsupported reduced-language constructor {kind}')

def stack_valid(ws, star=False):
    """Zero is the infinite truth tail of the theorem stack."""
    natural(ws)
    while ws:
        head,rest=unpair(ws)
        if not (value_star(head) if star else value(head)):return False
        assert rest<ws
        ws=rest
    return True

def instantiate_pattern(f, parameters):
    """Decode a constructor template as an ordinary first-order formula."""
    if type(f) is int:return decode(f)
    if isinstance(f,str):return decode(parameters[f])
    kind,a,b=f
    def label(x):return parameters[x] if isinstance(x,str) else x
    if kind=='imp':return ('imp',instantiate_pattern(a,parameters),instantiate_pattern(b,parameters))
    if kind=='rel':return ('mem',label(a),label(b))
    if kind=='all':return ('all',label(a),instantiate_pattern(b,parameters))
    raise ValueError(f'unsupported constructor {kind}')

def semantic_value(f, member, domain, env):
    """Ordinary first-order semantics for finite regression cases."""
    if f==TOP:return True
    if f[0]=='mem':return member(env[f[1]],env[f[2]])
    if f[0]=='imp':return not semantic_value(f[1],member,domain,env) or semantic_value(f[2],member,domain,env)
    if f[0]=='all':return all(semantic_value(f[2],member,domain,env|{f[1]:x}) for x in domain)
    raise ValueError(f)

