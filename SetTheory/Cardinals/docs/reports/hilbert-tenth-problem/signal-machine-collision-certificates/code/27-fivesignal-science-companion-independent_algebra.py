"""Independent exact algebra of stated affine formulas, never a signal simulator.
No collision search, trajectory integration, stored word, or upstream import.
"""
from fractions import Fraction as F
import json
from pathlib import Path

# Linear forms in D, X=x-D/3, Y=y-2D/3.
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def mul(c,a): return tuple(c*x for x in a)
D=(F(1),F(0),F(0)); X=(F(0),F(1),F(0)); Y=(F(0),F(0),F(1))
x=add(mul(F(1,3),D),X); y=add(mul(F(2,3),D),Y)
zero=(F(0),)*3
rows=[]; clock=zero

def translate(x,other,c):
    # Algebra only: T_c = H_(1-c) o L_(1/(1-c)).
    scaled=mul(1/(1-c),x)
    out=add(x,mul(c,other))
    duration=add(mul(2,add(x,scaled)),mul(2,other))
    return out,duration

def centered(a,b,c):
    global clock
    rows.extend([b,sub(D,b),a,sub(b,a)])
    for unused in range(2):
        a,duration=translate(a,b,c);clock=add(clock,duration)
        rows.extend([a,sub(b,a)])
        a,duration=translate(a,D,-F(2,3)*c);clock=add(clock,duration)
        rows.extend([a,sub(b,a)])
    return a

x=centered(x,y,-F(1,4))
clock=add(clock,D)
y=sub(D,centered(sub(D,y),sub(D,x),F(2,5)))
clock=add(clock,D)
x=centered(x,y,-F(1,4))
assert x==(F(1,3),F(3,5),-F(4,5))
assert y==(F(2,3),F(4,5),F(3,5))
# Three L_(1/2) homotheties cost 3 times the three unscaled targets.
clock=add(clock,mul(3,add(add(x,y),D)))
assert len(rows)==36
assert all(r[0]>0 for r in rows)
distances=[(r[0]*r[0]/(r[1]*r[1]+r[2]*r[2]),i,r) for i,r in enumerate(rows) if r[1] or r[2]]
minimum=min(z[0] for z in distances)
nearest=[z for z in distances if z[0]==minimum]
assert minimum==F(4,1845) and len(nearest)==1
q,i,r=nearest[0]
p=tuple(-r[0]*z/(r[1]*r[1]+r[2]*r[2]) for z in r[1:])
assert p==(F(4,205),-F(26,615))
# Return in coordinates D,X,Y is one-half times diag(1,R).
A=((F(1,2),0,0),(0,F(3,10),-F(2,5)),(0,F(2,5),F(3,10)))
# Solve k(I-A)=clock by exact Gaussian elimination on the transpose.
B=[[F(int(i==j))-A[j][i] for j in range(3)]+[clock[i]] for i in range(3)]
for col in range(3):
    pivot=next(j for j in range(col,3) if B[j][col])
    B[col],B[pivot]=B[pivot],B[col]
    fac=B[col][col];B[col]=[z/fac for z in B[col]]
    for j in range(3):
        if j!=col:
            fac=B[j][col];B[j]=[z-fac*w for z,w in zip(B[j],B[col])]
limitclock=tuple(B[i][-1] for i in range(3))
# Assert the geometric-series identity algebraically.
assert tuple(limitclock[i]-sum(limitclock[j]*A[j][i] for j in range(3)) for i in range(3))==clock
# Matrix in three positive section gaps (x,y-x,D-y).
M=((F(7,30),-F(1,15),F(1,3)),(F(7,15),F(11,30),-F(1,3)),(-F(1,5),F(1,5),F(1,2)))
# Coordinate change gap -> (D,X,Y).
C=((F(1),F(1),F(1)),(F(2,3),-F(1,3),-F(1,3)),(F(1,3),F(1,3),-F(2,3)))
def mm(a,b):return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))
assert mm(C,M)==mm(A,C)
# Gaussian rotation denominator lemma: residues (3,-4)^n stay (3,1) mod5.
assert ((3*3-1*1)%5,(2*3*1)%5)==(3,1)
receipt={'guard_count':len(rows),'nearest_guard_index_zero_based':i,'inradius_squared':str(minimum),'tangent_point':list(map(str,p)),'one_macro_clock_DXY':list(map(str,clock)),'zeno_time_DXY':list(map(str,limitclock)),'return_gap_matrix':[[str(v) for v in r] for r in M],'checks':'exact rational identities passed; no physical simulation'}
print(json.dumps(receipt,indent=2))
Path('/workspace/shared/signal-dimension-boundary57-20261004/independent-algebra-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
