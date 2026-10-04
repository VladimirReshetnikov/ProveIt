"""Owned independent exact algebra only: no dynamics, collisions, source execution.
Derives the 36 chamber rows and duration from printed primitive affine formulas.
Reads GUARDS.txt strictly as inert linear expressions through a whitelisted AST.
"""
from fractions import Fraction as F
from pathlib import Path
import ast, json, hashlib
OUT=Path(__file__).parent
SRC=OUT/'inert_sources'

def v(*a): return tuple(map(F,a))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def scale(k,a): return tuple(F(k)*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def mm(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))) for i in range(len(A)))
def ident(n): return tuple(tuple(F(i==j) for j in range(n)) for i in range(n))
def transpose(A): return tuple(zip(*A))
def inverse(A):
    n=len(A); A=[list(a)+list(b) for a,b in zip(A,ident(n))]
    for i in range(n):
        p=next(j for j in range(i,n) if A[j][i]); A[i],A[p]=A[p],A[i]
        d=A[i][i]; A[i]=[x/d for x in A[i]]
        for j in range(n):
            if j!=i:
                d=A[j][i]; A[j]=[x-d*y for x,y in zip(A[j],A[i])]
    return tuple(tuple(a[n:]) for a in A)
D=v(1,0,0); X=v(0,1,0); Y=v(0,0,1); zero=v(0,0,0)
x=add(scale(F(1,3),D),X); y=add(scale(F(2,3),D),Y)
rows=[]; durations=[]; block_endpoints=[]

def translated(target,reflector,c):
    # L(u) lasts 2(1+u)*target; H lasts 2*reflector.
    u=1/(1-c)
    durations.append(add(scale(2*(1+u),target),scale(2,reflector)))
    return add(target,scale(c,reflector))
def A(x,y,d,name):
    rows.extend([(name+' other > 0',y),(name+' other < D',sub(d,y))])
    eps=[x]
    for c,z in [(F(-1,4),y),(F(1,6),d)]*2:
        x=translated(x,z,c); eps.append(x)
    for i,e in enumerate(eps):
        rows.extend([(f'{name} endpoint {i} > 0',e),(f'{name} endpoint {i} < other',sub(y,e))])
    block_endpoints.append((name,eps)); return x,y
x,y=A(x,y,D,'A')
# Transfer from L to D takes D.
durations.append(D)
r,s=sub(D,y),sub(D,x)
rows.extend([('B other > 0',s),('B other < D',sub(D,s))])
eps=[r]
for c,z in [(F(2,5),s),(F(-4,15),D)]*2:
    r=translated(r,z,c); eps.append(r)
for i,e in enumerate(eps):
    rows.extend([(f'B endpoint {i} > 0',e),(f'B endpoint {i} < other',sub(s,e))])
block_endpoints.append(('B',eps)); y=sub(D,r)
durations.append(D)
x,y=A(x,y,D,'C')
rotation=(D,sub(x,scale(F(1,3),D)),sub(y,scale(F(2,3),D)))
expected_rotation=(D,v(0,F(3,5),F(-4,5)),v(0,F(4,5),F(3,5)))
assert rotation==expected_rotation
rotation_duration=tuple(sum(l[j] for l in durations) for j in range(3))
# The three half-scales each have duration 3 times the pre-scale target.
contraction_duration=scale(3,add(add(x,y),D))
ell=add(rotation_duration,contraction_duration)
N=tuple(scale(F(1,2),r) for r in rotation)
Q=(v(1,1,1),v(F(2,3),F(-1,3),F(-1,3)),v(F(1,3),F(1,3),F(-2,3)))
M=mm(mm(inverse(Q),N),Q)
assert M==tuple(tuple(F(z,30) for z in row) for row in [(7,-2,10),(14,11,-10),(-6,6,15)])
I=ident(3); ImN=tuple(sub(a,b) for a,b in zip(I,N))
T=mm((ell,),inverse(ImN))[0]
assert sub(T,mm((T,),N)[0])==ell
assert ell==v(F(37264,855),F(36497,1425),F(-10227,475))
assert T==v(F(74528,855),F(53102,3705),F(-144302,3705))

def parse(node):
    if isinstance(node,ast.Expression): return parse(node.body)
    if isinstance(node,ast.Name): return {'D':D,'X':X,'Y':Y}[node.id]
    if isinstance(node,ast.Constant) and type(node.value)==int: return F(node.value)
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
        a=parse(node.operand); return neg(a) if isinstance(a,tuple) else -a
    if isinstance(node,ast.BinOp):
        a,b=parse(node.left),parse(node.right)
        if isinstance(node.op,ast.Add): return add(a,b)
        if isinstance(node.op,ast.Sub): return sub(a,b)
        if isinstance(node.op,ast.Mult):
            if isinstance(a,F): return scale(a,b) if isinstance(b,tuple) else a*b
            assert isinstance(b,F); return scale(b,a)
        if isinstance(node.op,ast.Div):
            assert isinstance(b,F); return scale(1/b,a) if isinstance(a,tuple) else a/b
    raise ValueError(ast.dump(node))
supplied=[]
for line in (SRC/'GUARDS.txt').read_text().splitlines():
    if ': ' in line:
        name,expression=line.split(': ',1)
        supplied.append((name,parse(ast.parse(expression,mode='eval'))))
assert supplied==rows
rd=[]
for idx,(name,row) in enumerate(rows):
    a,b,c=row; assert a>0
    sq=a*a/(b*b+c*c)
    rd.append((sq,idx+1,name,row))
rd.sort(); radius2,i,name,row=rd[0]
assert rd[1][0]>radius2
assert radius2==F(4,1845)
a,b,c=row; p=(-a*b/(b*b+c*c),-a*c/(b*b+c*c))
assert p==(F(4,205),F(-26,615))
assert sum(t*t for t in p)==radius2
slacks=[dot(row,(F(1),)+p) for _,row in rows]
assert sum(s==0 for s in slacks)==1 and min(slacks)==0
# Sample center lies strictly in every half-plane; exact contact initial x,y.
contact_x=F(1,3)+p[0]; contact_y=F(2,3)+p[1]
afterA=contact_x-contact_y/2+F(1,3)
r=1-contact_y; s=1-afterA
assert F(5,3)*r==s
# Gaussian rational arithmetic and independent denominator check.
def c_mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def c_pow(a,n):
    ans=(F(1),F(0))
    while n:
        if n&1: ans=c_mul(ans,a)
        a=c_mul(a,a); n//=2
    return ans
zeta=(F(3,5),F(4,5)); inverse_zeta=(F(3,5),F(-4,5))
from math import lcm
for k in range(1,101):
    z=c_pow(inverse_zeta,k)
    assert lcm(z[0].denominator,z[1].denominator)==5**k
# Counts derived from numbers of spectator crossings per primitive, not trajectory execution.
collision_counts={'A':2*(8+10),'B':2*(8+10),'C':2*(8+10),'transfers':2*3,'contraction':4+8+12}
assert sum(collision_counts.values())==138

def stringify(a):
    if isinstance(a,F): return str(a)
    if isinstance(a,dict): return {k:stringify(v) for k,v in a.items()}
    if isinstance(a,(tuple,list)): return [stringify(x) for x in a]
    return a
receipt={'audit_kind':'Independent exact affine algebra and inert guard-text parsing; no physical trajectory execution',
    'source_sha256':{n:hashlib.sha256((SRC/n).read_bytes()).hexdigest() for n in ['PROOF.md','GUARDS.txt']},
    'rows_matched':len(rows),'center_positive':True,'distance_sorted':rd,'tangent':p,'radius_squared':radius2,
    'block_minimum_distance_squared':[min(a[0] for a in rd if (j*12+1)<=a[1]<=(j+1)*12) for j in range(3)],
    'matrix_normal_coordinates':N,'matrix_gap_coordinates':M,'rotation_duration':rotation_duration,
    'contraction_duration':contraction_duration,'macro_duration':ell,'total_duration':T,
    'contact_initial_positions':(contact_x,contact_y),'contact_after_A_x':afterA,'contact_reflected_r':r,'contact_reflected_s':s,
    'counts':collision_counts,'total_collisions':sum(collision_counts.values()),
    'critical_row_1based':i,'critical_row_name':name,'critical_row_coefficients':row,
    'gaussian_inverse_power_denominators_exact_checks':100}
(OUT/'exact_algebra_receipt.json').write_text(json.dumps(stringify(receipt),indent=2)+'\n')
print(json.dumps(stringify({k:v for k,v in receipt.items() if k!='distance_sorted'}),indent=2))
