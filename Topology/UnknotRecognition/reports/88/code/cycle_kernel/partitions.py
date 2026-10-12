"""Boundary connectivity partitions, with a right-division stabilization witness."""
from .model import Graph,DSU,components

def canonical(a):
    d={};return tuple(d.setdefault(x,len(d)) for x in a)

def boundary_partition(g:Graph):
    lab,_=components(g)
    return canonical([lab[x] for x in g.left+g.right])

def product(a,b):
    if len(a)!=len(b) or len(a)%2:raise ValueError('partition size mismatch')
    w=len(a)//2;d=DSU(3*w)
    for off,p in ((0,a),(w,b)):
        first={}
        for i,x in enumerate(p):
            if x in first:d.union(off+i,first[x])
            else:first[x]=off+i
    return canonical([d.find(i) for i in range(w)]+[d.find(2*w+i) for i in range(w)])

def rank(a):
    w=len(a)//2;return len(set(a[:w])&set(a[w:]))

def right_divisor(a,b):
    """Return x with b*x=a if b is a rank-preserving right multiple of a."""
    w=len(a)//2;d=DSU(2*w)
    ta=set(a[:w])&set(a[w:]); tb=set(b[:w])&set(b[w:])
    if len(ta)!=len(tb):raise ValueError('unequal ranks')
    for ca in ta:
        up=[i for i in range(w) if a[i]==ca]
        cb=b[up[0]]
        if [i for i in range(w) if b[i]==cb]!=up or cb not in tb:raise ValueError('upper blocks not preserved')
        chosen=next(i for i in range(w) if b[w+i]==cb)
        for j in range(w):
            if a[w+j]==ca:d.union(chosen,w+j)
    for ca in set(a[w:])-ta:
        low=[w+j for j in range(w) if a[w+j]==ca]
        for j in low[1:]:d.union(low[0],j)
    x=canonical([d.find(i) for i in range(2*w)])
    if product(b,x)!=canonical(a):raise ValueError('right division failed')
    return x

def stabilize(p):
    w=len(p)//2;a=canonical(p);ranks=[rank(a)]
    for s in range(1,w+2):
        b=product(a,p);ranks.append(rank(b))
        if rank(a)==rank(b):
            x=right_divisor(a,b)
            return dict(s=s,partition=list(a),successor=list(b),divisor=list(x),ranks=ranks)
        a=b
    raise AssertionError('rank descent exceeded width')

def verify_stabilization(p,cert):
    try:
        s=cert['s'];w=len(p)//2
        if type(s)is not int or not 1<=s<=w+1:return False
        a=canonical(p)
        for _ in range(s-1):a=product(a,p)
        b=product(a,p)
        return (a==tuple(cert['partition']) and b==tuple(cert['successor'])
                and rank(a)==rank(b) and product(b,tuple(cert['divisor']))==a)
    except (TypeError,KeyError,ValueError,IndexError):return False
