"""Small exact algebra fixtures and explicitly described braid closures.

These are tests, not representative hard-knot performance claims.
"""
from .slp import Arena, from_words


def free_reduce(word):
    out=[]
    for g in word:
        if out and out[-1]==-g: out.pop()
        else: out.append(g)
    return out


def inv(word):
    return [-g for g in reversed(word)]


def braid_closure(strands, word):
    if strands < 2: raise ValueError('at least two strands')
    images=[[i+1] for i in range(strands)]
    permutation=list(range(strands))
    for letter in word:
        i=abs(letter)-1
        if not 0 <= i < strands-1: raise ValueError('invalid braid generator')
        a,b=images[i],images[i+1]
        if letter>0:
            images[i],images[i+1]=free_reduce(a+b+inv(a)),a
        else:
            images[i],images[i+1]=b,free_reduce(inv(b)+a+b)
        permutation[i],permutation[i+1]=permutation[i+1],permutation[i]
    seen=set(); components=0
    for i in range(strands):
        if i in seen: continue
        components+=1; j=i
        while j not in seen:
            seen.add(j); j=permutation[j]
    p=from_words(strands,[(image,[i+1]) for i,image in enumerate(images)],
                 meridians=True,label=f'closure of {strands}-braid {list(word)}')
    return p,components


def trefoil():
    return from_words(2,[([1,2,1],[2,1,2])],meridians=True,label='trefoil: aba=bab')


def cyclic_meridians():
    return from_words(2,[([1],[2])],meridians=True,label='unknot: a=b')


def torus_nonmeridional():
    return from_words(2,[([1,1],[2,2,2])],label='trefoil, NONMERIDIONAL: x^2=y^3')


def huge_braid_relation(bits):
    """(ab)^m a=b(ab)^m, m=2^bits, the standard (2,2m+1) torus relation.

    The exponent is represented by repeated squaring. This is an algebraic
    capacity test, not an explicit crossing-diagram benchmark.
    """
    arena=Arena()
    a,b=arena.letter(1),arena.letter(2)
    word=arena.concat(a,b)
    for _ in range(bits): word=arena.concat(word,word)
    return arena.presentation(2,[(arena.concat(word,a),arena.concat(b,word))],
                              meridians=True,label=f'T(2,2^(1+{bits})+1) presentation')


def braid_wirtinger(strands, word):
    """Literal oriented braid crossing construction with bottom-to-top closure.

    A new variable is introduced only on the underpassing strand. Closure
    identifies its bottom arc with the matching top arc. This is independent
    of the Artin word-substitution fixture above (up to braid convention).
    """
    if strands < 2: raise ValueError('at least two strands')
    position=list(range(strands)); parent=list(range(strands)); crossings=[]
    permutation=list(range(strands))
    def root(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    for letter in word:
        i=abs(letter)-1
        if not 0 <= i < strands-1: raise ValueError('invalid braid generator')
        v=len(parent); parent.append(v)
        if letter>0:
            over,under=position[i],position[i+1]
            position[i],position[i+1]=v,over
        else:
            over,under=position[i+1],position[i]
            position[i],position[i+1]=over,v
        crossings.append((over,under,v,1 if letter>0 else -1))
        permutation[i],permutation[i+1]=permutation[i+1],permutation[i]
    for i,v in enumerate(position): parent[root(v)]=root(i)
    roots=sorted({root(i) for i in range(len(parent))})
    rename={v:i for i,v in enumerate(roots)}
    reduced=[tuple(rename[root(x)] for x in c[:3])+(c[3],) for c in crossings]
    components=0;seen=set()
    for i in range(strands):
        if i in seen:continue
        components+=1;j=i
        while j not in seen:seen.add(j);j=permutation[j]
    return len(roots),reduced,components
