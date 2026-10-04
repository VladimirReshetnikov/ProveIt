"""Fresh finite checks for periodic_packing_lemma.md; no upstream imports."""
import itertools
import json
import random
from pathlib import Path

RNG = random.Random(20261004)
B = 32

def geom(t, n):
    assert t >= 2 and n >= 0
    return (pow(t, n) - 1) // (t - 1)

def pack(vals, base=B):
    out = 0
    for a in reversed(vals):
        out = base * out + a
    return out

def idx(x, y, z, A, BB):
    return x + A*y + A*BB*z

def spread(T, beta, n, s):
    assert 0 <= T < beta**n and s >= n+1
    return (T * geom(beta**(s-1), n)) & ((beta-1) * geom(beta**s, n))

def boundary(vals, A, BB, C):
    return all(vals[idx(x,y,z,A,BB)] == 0
               for z in range(C) for y in range(BB) for x in range(A)
               if x in (0,A-1) or y in (0,BB-1) or z in (0,C-1))

def folded_test(U, radix, A, BB, C):
    X, Y, Z = radix**A, radix**(A*BB), radix**(A*BB*C)
    rx, ry = U % (X-1), U % (Y-1)
    return (rx % radix == 0 and radix*rx < X
            and ry % X == 0 and X*ry < Y
            and U % Y == 0 and Y*U < Z)

def check_uniform(p,q,r,Lx,Ly,Lz):
    tx=max(2, (q*r+2*Lx)//(2*Lx), (Ly*Lz+2*p)//(2*p))
    ty=max(2, (r+2*Ly)//(2*Ly), (Lz+2*q)//(2*q))
    tz=2
    a,bb,c=p*Lx*tx,q*Ly*ty,r*Lz*tz
    A,BB,C=2*a,2*bb,2*c
    X,Y,Z=B**A,B**(A*BB),B**(A*BB*C)
    tile=[RNG.randrange(6) for _ in range(p*q*r)]
    patch=[RNG.randrange(16) for _ in range(Lx*Ly*Lz)]
    Tile,Patch=pack(tile),pack(patch)
    T1=spread(Tile,B**p,q*r,A//p)
    T2=spread(T1,B**(A*q),r,BB//q)
    P1=spread(Patch,B**Lx,Ly*Lz,A//Lx)
    P2=spread(P1,B**(A*Ly),Lz,BB//Ly)
    expected_T2=sum(tile[idx(i,j,k,p,q)]*B**idx(i,j,k,A,BB)
                    for k in range(r) for j in range(q) for i in range(p))
    expected_P2=sum(patch[idx(i,j,k,Lx,Ly)]*B**idx(i,j,k,A,BB)
                    for k in range(Lz) for j in range(Ly) for i in range(Lx))
    assert T2 == expected_T2 and P2 == expected_P2
    H=T2*geom(B**p,A//p)*geom(B**(A*q),BB//q)*geom(B**(A*BB*r),C//r)
    expected_H=pack([tile[idx(x%p,y%q,z%r,p,q)]
                     for z in range(C) for y in range(BB) for x in range(A)])
    assert H == expected_H
    # Independently verify the fixed-literal polynomial/geometric formula.
    P=sum(pack(tile[p*(j+q*k):p*(j+q*k+1)])*X**j*Y**k
          for k in range(r) for j in range(q))
    Gx,Gy,Gz=(X-1)//(B**p-1),(Y-1)//(X**q-1),(Z-1)//(Y**r-1)
    assert P*Gx*Gy*Gz == H
    D=B**idx(a,bb,c,A,BB)*P2
    expected_D=sum(patch[idx(i,j,k,Lx,Ly)]*B**idx(a+i,bb+j,c+k,A,BB)
                   for k in range(Lz) for j in range(Ly) for i in range(Lx))
    assert D == expected_D
    assert 1<=a and a+Lx-1<=A-2 and 1<=bb and bb+Ly-1<=BB-2
    assert 1<=c and c+Lz-1<=C-2
    Jx,Jy,Jz=geom(B,A-2),geom(X,BB-2),geom(Y,C-2)
    assert B**2*((B-1)*Jx+1)==X
    assert X**2*((X-1)*Jy+1)==Y
    assert Y**2*((Y-1)*Jz+1)==Z
    I=B*X*Y*Jx*Jy*Jz
    ivals=[int(0<x<A-1 and 0<y<BB-1 and 0<z<C-1)
           for z in range(C) for y in range(BB) for x in range(A)]
    assert I == pack(ivals)
    vals=[0]*(A*BB*C)
    for _ in range(15):
        vals[idx(RNG.randrange(1,A-1),RNG.randrange(1,BB-1),RNG.randrange(1,C-1),A,BB)]=1
    U=pack(vals)
    assert (U&I)==U and U%Y==0 and Y*U<Z
    shifts=[B*U,U//B,X*U,U//X,Y*U,U//Y]
    directions=[(-1,0,0),(1,0,0),(0,-1,0),(0,1,0),(0,0,-1),(0,0,1)]
    for S,(dx,dy,dz) in zip(shifts,directions):
        expected=[]
        for z in range(C):
            for y in range(BB):
                for x in range(A):
                    xx,yy,zz=x+dx,y+dy,z+dz
                    expected.append(vals[idx(xx,yy,zz,A,BB)] if 0<=xx<A and 0<=yy<BB and 0<=zz<C else 0)
        assert S==pack(expected)
    return A*BB*C

uniform_cases=0
largest_volume=0
for dims in itertools.product((1,2),repeat=6):
    largest_volume=max(largest_volume,check_uniform(*dims))
    uniform_cases+=1

spread_cases=0
for n in range(1,8):
    for s in range(n+1,n+4):
        for beta in (2,4,32,1024):
            vals=[RNG.randrange(beta) for _ in range(n)]
            assert spread(pack(vals,beta),beta,n,s)==sum(v*beta**(s*i) for i,v in enumerate(vals))
            spread_cases+=1

fold_cases=0
for A,BB,C in ((2,2,2),(3,3,3),(3,4,3),(4,3,4)):
    N=A*BB*C
    K=2
    radix=N*K+2
    for trial in range(60):
        vals=[RNG.randrange(K+1) for _ in range(N)]
        if trial%2:
            vals=[v if (0<x<A-1 and 0<y<BB-1 and 0<z<C-1) else 0
                  for v,(z,y,x) in zip(vals,itertools.product(range(C),range(BB),range(A)))]
        assert folded_test(pack(vals,radix),radix,A,BB,C)==boundary(vals,A,BB,C)
        fold_cases+=1
for bits in range(256):
    vals=[(bits>>i)&1 for i in range(8)]
    assert folded_test(pack(vals,10),10,2,2,2)==boundary(vals,2,2,2)
    fold_cases+=1

# Exhibit a false positive if the growing-radix hypothesis is omitted.
A,BB,C=3,10,6
vals=[0]*(A*BB*C)
for y in range(1,9):
    for z in range(1,5):
        vals[idx(0,y,z,A,BB)]=1
assert not boundary(vals,A,BB,C)
assert folded_test(pack(vals),B,A,BB,C)

# A genuine one-toppling endpoint fixture in a zero background.
A=BB=C=4
X,Y=B**A,B**(A*BB)
center=idx(2,2,2,A,BB)
U=B**center
D=6*U
F=B*U+U//B+X*U+U//X+Y*U+U//Y
assert D+B*U+U//B+X*U+U//X+Y*U+U//Y == 6*U+F
assert all(((F>>(5*i))&31)<=5 for i in range(A*BB*C))

receipt={
    "status":"passed",
    "uniform_reshape_background_patch_mask_neighbor_cases":uniform_cases,
    "largest_uniform_test_volume":largest_volume,
    "independent_block_spread_cases":spread_cases,
    "growing_radix_fold_boundary_cases":fold_cases,
    "fixed_radix_folding_counterexample_confirmed":True,
    "stable_endpoint_fixture":"one legal toppling at (2,2,2) in 4x4x4 zero background",
    "upstream_code_executed":False,
    "universal_loader_authenticated":False
}
path=Path(__file__).with_name("verification_receipt.json")
path.write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt,indent=2))
