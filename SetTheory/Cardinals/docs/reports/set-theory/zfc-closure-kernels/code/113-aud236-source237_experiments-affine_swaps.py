"""Exact affine semantics for a sound, restricted class of closed programs.

Recognizes increments, total unary transfer loops and their closed sequences.
An accepted matrix identity is a theorem for all natural register values;
the limited recognizer deliberately rejects all other control fragments.
"""
import source_core as e
from functools import cache
from collections import defaultdict

DIM=10
IDENTITY=tuple(tuple(int(i==j) for j in range(DIM)) for i in range(DIM))
def compose(a,b):
    """Execute a then b (column vector convention)."""
    return tuple(tuple(sum(b[i][k]*a[k][j] for k in range(DIM)) for j in range(DIM)) for i in range(DIM))

@cache
def affine(n):
    x=e.S[n]
    if isinstance(x[0],str):
        if x[0]!='CI':return None
        m=[list(row) for row in IDENTITY];m[x[1]][-1]+=1
        return tuple(map(tuple,m))
    aa,bb=affine(x[0]),affine(x[1])
    if aa is not None and bb is not None:return compose(aa,bb)
    if e.boundary(n)!=(0,0,False):return None
    pp=e.paths(n)
    if len(pp)<2 or pp[0][0]!='0' or pp[0][1]!='CD':return None
    counter=pp[0][2];body=pp[1:-1];last=pp[-1]
    if last[1]!='CC' or last[2]!=last[0].count('1'):return None
    if any(op!='CI' or r==counter for path,op,r in body):return None
    m=[list(row) for row in IDENTITY];m[counter]=[0]*DIM
    for path,op,r in body:m[r][counter]+=1
    return tuple(map(tuple,m))

def commuting(n):
    x=e.S[n]
    if isinstance(x[0],str):return False
    aa,bb=affine(x[0]),affine(x[1])
    return aa is not None and bb is not None and x[0]!=x[1] and compose(aa,bb)==compose(bb,aa)

if __name__=='__main__':
    groups=defaultdict(list)
    for n in e.live(e.ROOT):
        aa=affine(n)
        if aa is not None:groups[aa].append(n)
    print('Recognized',sum(map(len,groups.values())),'of',len(e.live(e.ROOT)))
    print('Equivalent closed nodes',[v for v in groups.values() if len(v)>1])
    print('Commuting nodes',[n for n in e.live(e.ROOT) if commuting(n)])
