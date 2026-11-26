"""Certify strict consecutive-column interlacing for all integer n >= m.
Requires verify_ehrhart.py in the same directory and only Python's standard library.
"""
from argparse import ArgumentParser
from math import gcd
from time import monotonic
from verify_ehrhart import normalized_coords


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):
            result[i+j] += v*w
    return result


def transition(r, n):
    a, b = normalized_coords(r, n)
    c, d = normalized_coords(r, n+1)
    ac = multiply(a,c)
    cb = [0] + multiply(c,b)
    bd = multiply(b,d)
    # The leading entry of the padded b is always zero, hence cb[-1]=0.
    assert cb[-1] == 0
    coeff = [n*n*u-v+w for u,v,w in zip(ac,cb,bd)]
    assert all(v==0 for v in coeff[1::2])
    return coeff[::2]


def primitive(p):
    while p and not p[-1]:
        p.pop()
    if p:
        content = gcd(*p)
        return [v//content for v in p]
    return []


def remainder(a,b):
    """Positive multiple of the rational remainder, preserving its sign."""
    while len(a)>=len(b):
        offset = len(a)-len(b)
        lead = a[-1] if b[-1]>0 else -a[-1]
        a = [v*abs(b[-1]) for v in a]
        for j,v in enumerate(b):
            a[j+offset] -= lead*v
        a = primitive(a)
    return a


def changes(sequence):
    nonzero=[v>0 for v in sequence if v]
    return sum(x!=y for x,y in zip(nonzero, nonzero[1:]))


def positive_on_halfline(p):
    """Prove strict positivity on [0,infinity) by Sturm's theorem."""
    p = primitive(list(p))
    if not p or p[0]<=0:
        return False
    chain=[p]
    q=primitive([i*p[i] for i in range(1,len(p))])
    while q:
        p,q=q,[-v for v in remainder(p,q)]
        chain.append(p)
    return changes([f[0] for f in chain])==changes([f[-1] for f in chain])


def certify_interlacing(m):
    # verify_ehrhart.py establishes coordinate degrees r and r+1.
    r=m-1
    assert positive_on_halfline(transition(r,m-1))  # adjacent square boundary
    rows=[transition(r,m+j) for j in range(2*r+3)]
    assert positive_on_halfline(rows[0])
    count=0
    while rows:
        first=rows[0]
        if any(first):
            assert positive_on_halfline(first), (m,count)
            count+=1
        rows=[[v-u for u,v in zip(a,b)] for a,b in zip(rows,rows[1:])]
    return count


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable certificate assertions')
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('first',type=int,nargs='?',default=6)
    parser.add_argument('last',type=int,nargs='?',default=None)
    args=parser.parse_args()
    for m in range(args.first,(args.last or args.first)+1):
        start=monotonic()
        print(f'm={m}  positive Newton polynomials={certify_interlacing(m)}'
              f'  seconds={monotonic()-start:.2f}',flush=True)
