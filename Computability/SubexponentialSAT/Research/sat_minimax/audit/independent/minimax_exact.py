#!/usr/bin/env python3
"""Exact minimax certificates for fixed menus of nonnegative linear costs.

This is a finite-dimensional certificate tool, not a SAT solver.
For finite nonempty supports V[j] in Q_{>=0}^d it computes exactly
  Lambda^2, Lambda=max_{g>=0, ||g||_2<=1} min_j max_{v in V[j]} dot(v,g).
The result is exact for that Euclidean relaxation only.
Standard library only; no floating point is used for certification.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import argparse, json


def dot(x,y):
    return sum((a*b for a,b in zip(x,y)),F(0))


def solve(A,b):
    """Exact square linear system, or None when singular."""
    n=len(A); a=[list(map(F,row))+[F(rhs)] for row,rhs in zip(A,b)]
    if any(len(row)!=n+1 for row in a):raise ValueError('nonsquare system')
    for c in range(n):
        k=next((r for r in range(c,n) if a[r][c]),None)
        if k is None:return None
        a[c],a[k]=a[k],a[c]
        z=a[c][c]; a[c]=[v/z for v in a[c]]
        for r in range(n):
            if r!=c and a[r][c]:
                z=a[r][c];a[r]=[u-z*v for u,v in zip(a[r],a[c])]
    return [a[r][-1] for r in range(n)]


def check_closest(points,weights):
    """Necessary/sufficient exact KKT certificate for the closest hull point."""
    if len(points)!=len(weights) or not points:return False
    if any(p<0 for p in weights) or sum(weights)!=1:return False
    d=len(points[0])
    w=tuple(sum((p*v[k] for p,v in zip(weights,points)),F(0)) for k in range(d))
    n2=dot(w,w)
    if any(dot(v,w)<n2 for v in points):return False
    if any(p and dot(v,w)!=n2 for p,v in zip(weights,points)):return False
    return w,n2


def closest(points):
    """Enumerate affinely independent active subsets of rational support vectors."""
    points=tuple(tuple(map(F,v)) for v in points)
    if not points:raise ValueError('empty hull')
    d=len(points[0]);q=len(points)
    if any(len(v)!=d for v in points):raise ValueError('dimension mismatch')
    for k in range(1,min(d+1,q)+1):
        for face in combinations(range(q),k):
            G=[[dot(points[i],points[j]) for j in face] for i in face]
            # G p = t 1, 1^T p = 1. For an affinely independent subset the
            # augmented matrix is invertible, including when its affine hull
            # contains the origin.
            A=[row+[-F(1)] for row in G]+[[F(1)]*k+[F(0)]]
            z=solve(A,[F(0)]*k+[F(1)])
            if z is None or any(p<0 for p in z[:k]):continue
            weights=[F(0)]*q
            for i,p in zip(face,z[:k]):weights[i]=p
            checked=check_closest(points,weights)
            if checked:
                w,n2=checked
                if n2!=z[k]:raise ArithmeticError('KKT scalar mismatch')
                return {'weights':tuple(weights),'point':w,'norm_squared':n2,'active_face':face}
    raise ArithmeticError('no certifying face found')


def normalize_menu(menu):
    menu=tuple(tuple(tuple(map(F,v)) for v in support) for support in menu)
    if not menu or any(not V for V in menu):raise ValueError('empty menu or support')
    d=len(menu[0][0])
    if not d or any(len(v)!=d for V in menu for v in V):raise ValueError('bad dimension')
    if any(a<0 for V in menu for v in V for a in v):raise ValueError('negative support coordinate')
    return menu


def exact_menu(menu):
    menu=normalize_menu(menu)
    certs=[];best=None
    for indices in product(*(range(len(V)) for V in menu)):
        points=tuple(V[i] for V,i in zip(menu,indices))
        cert=closest(points);cert['indices']=indices
        certs.append(cert)
        if best is None or cert['norm_squared']>best['norm_squared']:best=cert
    if len(certs)!=prod(map(len,menu)):raise ArithmeticError('incomplete enumeration')
    return {'dimension':len(menu[0][0]),'strategy_count':len(menu),
            'support_counts':list(map(len,menu)),'tuple_count':len(certs),
            'lambda_squared':best['norm_squared'],'maximizing_tuple':best,
            'all_tuple_certificates':certs}


def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,(tuple,list)):return [serial(y) for y in x]
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    return x


def tests():
    cases=[('orthogonal_two',[[[1,0]],[[0,1]]],F(1,2)),
           ('unequal_two',[[[2,0]],[[0,1]]],F(4,5)),
           ('orthogonal_three',[[[1,0,0]],[[0,1,0]],[[0,0,1]]],F(1,3)),
           ('finite_support_choice',[[[1,0],[0,1]],[[2,0],[0,2]]],F(1)),
           ('zero_strategy',[[[0,0]],[[1,1]]],F(0)),
           ('duplicate_vectors',[[[1,0]],[[1,0]],[[0,1]]],F(1,2))]
    out=[]
    for name,menu,want in cases:
        got=exact_menu(menu)
        if got['lambda_squared']!=want:raise AssertionError((name,got,want))
        out.append({'case':name,'lambda_squared':str(want),'tuple_count':got['tuple_count']})
    # A local upper certificate alone need not be a closest point.
    if check_closest(((F(2),F(0)),(F(0),F(1))),(F(1,2),F(1,2))):
        raise AssertionError('nonoptimal equal averaging was accepted')
    try: exact_menu([[[-1,0]],[[0,1]]])
    except ValueError: pass
    else: raise AssertionError('negative coordinate accepted')
    return {'status':'passed','cases':out,
            'strict_weighted_example':{'equal_average_squared':'5/4','optimal_squared':'4/5',
                'weights':['1/5','4/5']}}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--menu',help='JSON file: array of supports, each an array of vectors')
    ap.add_argument('--output',help='Output JSON path (otherwise stdout)')
    args=ap.parse_args()
    result=exact_menu(json.load(open(args.menu))) if args.menu else tests()
    txt=json.dumps(serial(result),indent=2)+'\n'
    if args.output:open(args.output,'w').write(txt)
    else:print(txt,end='')
