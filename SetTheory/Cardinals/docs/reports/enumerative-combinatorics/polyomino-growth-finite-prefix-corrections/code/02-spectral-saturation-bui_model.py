"""Exact 17-variable map transcribed from ProveIt's model.py (see SOURCES.md).
The independent Jacobian evaluator below differentiates each monomial occurrence.
"""
from fractions import Fraction
from pathlib import Path
import csv
NAMES='c d e f g h p q r s t u v w x y z'.split()
TERMS=[[(1,()),(1,(2,))],[(1,()),(1,(4,))],[(1,()),(1,(3,))],
[(0,(4,)),(0,(6,))],[(0,(2,)),(0,(7,))],[(0,(1,)),(0,(9,))],
[(0,(2,5)),(0,(7,1)),(0,(14,8)),(0,(12,15)),(0,(11,15,16))],
[(1,(4,)),(1,(4,2)),(2,(11,)),(2,(10,4)),(2,(8,11))],
[(0,(15,)),(0,(13,))],
[(1,(4,)),(1,(2,2)),(2,(10,)),(2,(14,4)),(2,(15,11))],
[(0,(14,)),(0,(12,))],
[(0,(1,5)),(0,(9,1)),(0,(15,8)),(0,(13,15)),(0,(11,16,16))],
[(1,(9,)),(2,(4,4)),(2,(10,2)),(2,(8,10))],
[(1,(9,)),(2,(2,4)),(2,(14,2)),(2,(15,10))],
[(1,(1,)),(2,(4,)),(2,(11,))],
[(1,(0,)),(2,(4,)),(2,(10,))],
[(1,(0,)),(2,(2,)),(2,(14,))]]

def load_profiles(path: Path):
    with path.open(newline='') as f:
        rows=list(csv.DictReader(f))
    if [int(r['n']) for r in rows] != list(range(1,19)):
        raise ValueError('Expected all sizes 1 through 18')
    return [[0]+[int(r[k]) for r in rows] for k in NAMES]

def horner(p,t):
    y=0
    for a in reversed(p): y=y*t+a
    return y

def jacobian(t,a):
    J=[[0 for j in NAMES] for i in NAMES]
    for i,row in enumerate(TERMS):
        for power,inds in row:
            for pos,j in enumerate(inds):
                v=t**power
                for k,q in enumerate(inds):
                    if k!=pos: v*=a[q]
                J[i][j]+=v
    return J

def matvec(J,v):
    return [sum(a*b for a,b in zip(row,v)) for row in J]
