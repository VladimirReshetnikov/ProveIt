"""Independent support reconstruction, exhaustive norm and recurrence audit.
Author-written iteration-3 code. Does not import/read/execute archive programs.
"""
from fractions import Fraction as F
from itertools import permutations,combinations
from operator import add
from math import isqrt
import json

L=1400000;D=1400007;V=1175014;W=750000
MENUS={9:[[[0,1,2],[3,4,5],[6,7,8]],[[0,3,6],[1,4,7],[2,5,8]],[[0,4,8],[1,5,6],[2,3,7]],[[0,5,7],[1,3,8],[2,4,6]]],
13:[[[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],[[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],[[0,8,11,12,1],[7,10,4,3],[5,2,6,9]],[[3,8,0,5,10],[2,7,12,4],[9,1,6,11]]]}
EXPECTED={9:(57,405850918811760,F(563681831683,1764000000000)),13:(89,895372728026656,F(27980397750833,82810000000000))}
def require(x,msg):
    if not x:raise ArithmeticError(msg)
def make_supports(r,plan):
    require(sorted(v for b in plan for v in b)==list(range(r)),'plan not partition')
    full=(1<<r)-1;mask=lambda b:sum(1<<v for v in b)
    operations=[];pending=[tuple(b) for b in plan]
    while pending:
        block=pending.pop()
        if len(block)<=1:continue
        mid=len(block)//2;a,b=block[:mid],block[mid:]
        operations.append((mask(a),mask(b),full^mask(block)))
        pending.extend((a,b))
    operations.append(tuple(mask(b) for b in plan))
    allforms=set()
    weights=set(permutations((D,D,0)))|set(permutations((L,V,W)))
    edges=list(combinations(range(r),2))
    for parts in operations:
        classes=[]
        for u,v in edges:
            iu=next(j for j,p in enumerate(parts) if p&(1<<u))
            iv=next(j for j,p in enumerate(parts) if p&(1<<v))
            pair=tuple(sorted((iu,iv)))
            classes.append(None if iu==iv else {(0,1):0,(0,2):1,(1,2):2}[pair])
        for w in weights:allforms.add(tuple(0 if cl is None else w[cl] for cl in classes))
    return sorted(allforms)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def audit(r):
    ss=[make_supports(r,p) for p in MENUS[r]]
    n,Q,b2=EXPECTED[r];require(all(len(s)==n for s in ss),'support counts')
    # Deliberately reorder enumeration relative to primary verifier.
    order=(0,2,1,3);ss=[ss[j] for j in order]
    norms=[[dot(v,v) for v in vs] for vs in ss]
    cross={(i,j):[[2*dot(a,b) for b in ss[j]] for a in ss[i]] for i,j in combinations(range(4),2)}
    best=-1;where=None;count=0
    for a in range(n):
        for b in range(n):
            prefix=norms[0][a]+norms[1][b]+cross[0,1][a][b]
            right=[norms[3][d]+cross[0,3][a][d]+cross[1,3][b][d] for d in range(n)]
            for c in range(n):
                base=prefix+norms[2][c]+cross[0,2][a][c]+cross[1,2][b][c]
                vals=list(map(add,right,cross[2,3][c]))
                local=max(vals);count+=n
                if base+local>best:best=base+local;where=(a,b,c,vals.index(local))
    direct=sum(sum(ss[j][where[j]][e] for j in range(4))**2 for e in range(r*(r-1)//2))
    require(count==n**4 and best==direct==Q,'exhaustive norm/witness')
    derived=F(2*best,4**2*r*r*L*L)
    require(derived==b2,'averaging/directed factor')
    if r==9:
        for u,v in combinations(range(r),2):
            require(sum(any(u in b and v in b for b in p) for p in MENUS[r])==1,'affine pair coverage')
    return {'r':r,'supports':n,'quadruples':count,'Q':best,'b_squared':str(derived),'witness_reordered':where,'enumeration_order':order}
def sq(x):
    x=F(x);d=10**32;q=isqrt(x.numerator*d*d//x.denominator)
    return F(q,d),F(q+1,d)
def at(i):
    x=F(1,i);s=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(64)),F(0))
    return s,s+x**129/129
a,b=at(5);c,d=at(239);pl,ph=16*a-4*d,16*b-4*c
lnlo=2*sum((F(1,(2*k+1)*3**(2*k+1)) for k in range(64)),F(0));lnhi=lnlo+F(9,4*129*3**129)
kl,kh=pl*sq(2)[0]/lnhi,ph*sq(2)[1]/lnlo
# Compute normalized factors as square roots, avoiding interval division chains.
f0,f1,f2=F(1577,100000),F(2813,250000),F(1433,300000)
b9,b13=EXPECTED[9][2],EXPECTED[13][2]
terms=[[b9/f0],[F(16,81)/f0,b13*F(4,81)/f1],[F(16,81)/f0,F(24,169)*F(4,81)/f1,F(3,4)*F(16,117**2)/f2]]
intervals=[]
for row in terms:
    lo=sum((sq(t)[0] for t in row),F(0))*kl;hi=sum((sq(t)[1] for t in row),F(0))*kh
    intervals.append((lo,hi))
require(intervals[2][0]>max(intervals[0][1],intervals[1][1]),'paid infinite tail dominates')
require(intervals[2][1]<F(30492,1000) and intervals[0][1]<F(28854,1000),'safe generic resources')
space1=kh*sq(b13*F(4,81)/f1)[1];space2=kh*sq(F(632,1225)*F(16,117**2)/f2)[1]
require(intervals[0][0]>max(space1,space2),'root storage dominates')
require(9**1577<2**5000 and 13**13511<2**50000 and 7**1781<2**5000,'unchanged strict packing')
print(json.dumps({'scope':'Independent bit-mask operation supports, reordered exhaustive integer Gram search, coordinate witness, directed averaging factor and rational recurrence; no incoming program execution.',
'certificates':[audit(r) for r in (9,13)],'generic_interval_displays':[[float(a),float(b)] for a,b in intervals],
'safe_eventual_time':'30.492','safe_eventual_space':'28.854'},indent=2))
