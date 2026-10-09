"""Literal free-group word utilities and a capped Artin braid presentation."""
from __future__ import annotations

class ResourceLimit(RuntimeError):
    pass

def inverse(w):
    return tuple(-x for x in reversed(w))

def reduce_word(w):
    out=[]
    for x in w:
        if type(x) is not int or not x: raise ValueError('letters are nonzero strict integers')
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return tuple(out)

def cyclic_reduce(w):
    w=reduce_word(w); i=0; j=len(w)
    while i<j and w[i]==-w[j-1]: i+=1; j-=1
    return w[i:j]

def primitive_period(w):
    n=len(w)
    if not n: return 0
    pi=[0]*n
    for i in range(1,n):
        j=pi[i-1]
        while j and w[i]!=w[j]: j=pi[j-1]
        if w[i]==w[j]: j+=1
        pi[i]=j
    p=n-pi[-1]
    return p if n%p==0 else n

def validate_braid(strands, braid):
    if type(strands) is not int or strands<1: raise ValueError('positive strand count required')
    if not isinstance(braid,(list,tuple)): raise ValueError('braid must be a list or tuple')
    if any(type(x) is not int or not 0<abs(x)<strands for x in braid): raise ValueError('invalid crossing')
    if strands>len(braid)+1: raise ValueError('too few crossings for a knot closure')
    p=list(range(strands))
    for x in braid:
        i=abs(x)-1; p[i],p[i+1]=p[i+1],p[i]
    seen=set(); x=0
    while x not in seen: seen.add(x); x=p[x]
    if len(seen)!=strands: raise ValueError('closure is not a knot')

def braid_presentation(strands,braid,*,letter_cap=200_000):
    if type(letter_cap) is not int or letter_cap<1: raise ValueError('positive letter cap required')
    if type(strands) is int and strands>letter_cap: raise ResourceLimit('strand allowance')
    validate_braid(strands,braid)
    images=[(i+1,) for i in range(strands)]
    for c in braid:
        i=abs(c)-1; a,b=images[i:i+2]
        length=2*len(a)+len(b) if c>0 else len(a)+2*len(b)
        if length+sum(map(len,images))>letter_cap: raise ResourceLimit('Artin word allowance')
        if c>0: images[i:i+2]=[reduce_word(a+b+inverse(a)),a]
        else: images[i:i+2]=[b,reduce_word(inverse(b)+a+b)]
    return [cyclic_reduce(w+(-i-1,)) for i,w in enumerate(images)]

def difference_basis(relators,anchor):
    """x_anchor=t and x_i=y_i t, with t retaining the anchor identifier."""
    out=[]
    for w in relators:
        expanded=[]
        for x in w:
            g=abs(x)
            image=(anchor,) if g==anchor else (g,anchor)
            expanded.extend(image if x>0 else inverse(image))
        out.append(cyclic_reduce(expanded))
    return out
