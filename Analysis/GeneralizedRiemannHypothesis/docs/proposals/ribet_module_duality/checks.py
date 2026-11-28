"""Exact finite-model checks; the paper proves the general claims."""
from itertools import product
import random
import sympy as S


def add(x,y,mods): return tuple((a+b)%m for a,b,m in zip(x,y,mods))
def mul(a,x,mods): return tuple((a*b)%m for b,m in zip(x,mods))
def extend_group(W,x,mods):
    return frozenset(add(w,mul(k,x,mods),mods) for w in W for k in range(max(mods)))

# All subgroups of Z/9 + Z/3; explicit dual into Z/9.
mods=(9,3); A=9
V=list(product(*(range(m) for m in mods)))
D=list(product(*(range(0,A,A//m) for m in mods)))
zero=(0,0)
groups={frozenset([zero])}; queue=list(groups)
while queue:
    W=queue.pop()
    for x in V:
        W1=extend_group(W,x,mods)
        if W1 not in groups:
            groups.add(W1); queue.append(W1)
def ev(f,x): return sum(a*b for a,b in zip(f,x))%A
assert len(D)==len(V)
for W in groups:
    Wlist=sorted(W)
    restrictions={tuple(ev(f,x) for x in Wlist) for f in D}
    ann=[f for f in D if all(ev(f,x)==0 for x in W)]
    assert len(restrictions)==len(W)
    assert len(ann)*len(W)==len(D)
    assert {x for x in V if all(ev(f,x)==0 for f in ann)}==set(W)
print(f"DVR duality: all {len(groups)} subgroups of Z/9 + Z/3; exact annihilators and restrictions OK")
# Nonspanning evaluation set: only first coordinate evaluated.
assert len({ev(f,(1,0)) for f in D})==9 and len(D)==27
print("Nonspanning evaluations: full dual has 27 elements, function module has 9")

# Polynomial determinant transport, including repeated v rows.
x=S.symbols('X'); rng=random.Random(8112026)
for d in range(1,5):
    for rep in range(8):
        def poly(): return rng.randint(-3,3)+rng.randint(-2,2)*x
        Q=S.Matrix(d,d,lambda i,j:poly())
        v=S.Matrix(1,d,lambda i,j:poly())
        a=3*x+1
        b=[poly() for _ in range(d)]
        M=S.Matrix(d,d,lambda i,j:Q[i,j]+b[i]*v[j])
        rhs=a*Q.det()
        for i in range(d):
            T=Q.copy(); T[i,:]=a*v
            rhs+=b[i]*T.det()
        assert S.expand(a*M.det()-rhs)==0
print("Determinant transport: 32 exact polynomial identities")

# Nontrivial triangular example from the paper's setup.
# O=Z_(3), p=3^4, C=3^2; N=<p e1,p e2,p e3,e3-X e2,C e3>.
# y_tau=e3, y_phi=e2, y_tau'=y_phi'=0; B detects 3e1.
p=3**4; C=3**2; d=3; I=1
Z=list(product(range(p),range(p),range(0,p,p//C)))
ZB=[f for f in Z if 3*f[0]%p==0]
Sstar=[f for f in ZB if f[1]==0 and f[2]==0]
assert all(C*f[2]%p==0 for f in ZB)
assert all(all(C*t%p==0 for t in f) for f in Sstar)
assert len(Z)//len(ZB)==3**3 and len(Sstar)==3
H=S.Matrix([[3,0,0],[0,1,0],[0,-x,1]])
F=3**3*C*H.det()
Nrows=S.Matrix([[p,0,0],[0,0,C],[0,-x,1]])
assert S.expand(F*x-Nrows.det())==0
v=0; f=int(F)
while f%3==0: v+=1;f//=3
assert v==3+2+1 and v<3+(I+d)*2
print(f"Triangular example: v(F(0))={v}; old bound=11; exact certificate det(Nrows)=F*X")

# Direct CH in the matrix-coefficient quotient Q=M_2(Q), with a=0.
# Build By=B1 y rho0 exactly and test y_i P(rho0)=0.
def randmat(): return S.Matrix(2,2,lambda i,j:rng.randint(-3,3))
def flatten(blocks): return S.BlockMatrix(blocks).as_explicit()
for k in range(12):
    rho0=randmat(); y=[S.eye(2),randmat()]
    B1=[[randmat(),randmat()],[randmat(),randmat()]]
    B=[]
    for i in range(2):
        b2=randmat()
        B.append([(B1[i][0]*y[0]+B1[i][1]*y[1])*rho0-b2*y[1],b2])
        assert B[i][0]*y[0]+B[i][1]*y[1]==(B1[i][0]*y[0]+B1[i][1]*y[1])*rho0
    P=S.Poly(flatten([[B[i][j]-x*B1[i][j] for j in range(2)] for i in range(2)]).det(),x)
    PR=S.zeros(2)
    for (j,),c in P.terms(): PR+=c*rho0**j
    assert all(Y*PR==S.zeros(2) for Y in y)
    assert P.eval(0)==flatten(B).det()
print("Direct Ribet polynomial: 12 noncommutative block examples OK")
print("All checks passed. These are finite regressions, not a Lean replay.")
