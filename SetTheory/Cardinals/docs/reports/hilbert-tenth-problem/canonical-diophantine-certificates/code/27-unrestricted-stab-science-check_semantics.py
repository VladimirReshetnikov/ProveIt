#!/usr/bin/env python3
"""Fresh finite semantic regressions; no earlier code imports or executions.

The explicit POWER theorem remains an inherited dependency. These tests do not
construct its astronomical nested witnesses and are not a proof by enumeration.
"""
from collections import defaultdict, deque
import hashlib
from itertools import product
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent
DIRECTIONS=((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))

def require(condition, message):
    if not condition: raise RuntimeError(message)

def G(base,length): return (base**length-1)//(base-1)
def pack(digits,base): return sum(d*base**i for i,d in enumerate(digits))
def spread(code,base,length,stride):
    require(length>=1 and stride>=length+1,'spread domain')
    require(0<=code<base**length,'spread input range')
    return code*G(base**(stride-1),length) & ((base-1)*G(base**stride,length))
def translate(v,d): return tuple(a+b for a,b in zip(v,d))
def encode(fields):
    result=fields[-1]
    for a in reversed(fields[:-1]):
        total=a+result
        result=total*(total+1)//2+result
    return result+1

def stabilize(initial):
    chips=defaultdict(int,initial)
    pending=deque(v for v,n in chips.items() if n>=6)
    counts=defaultdict(int)
    trace=[]
    while pending:
        v=pending.popleft()
        if chips[v]<6: continue
        require(len(trace)<100000,'finite fixture exceeded safeguard')
        chips[v]-=6; counts[v]+=1; trace.append(v)
        for direction in DIRECTIONS:
            w=translate(v,direction)
            chips[w]+=1
            if chips[w]==6: pending.append(w)
        if chips[v]>=6:pending.append(v)
    return dict(counts),dict(chips),trace

def fixture(pqr,def_,tile,patch,U,L=None):
    p,q,r=pqr;d,e,f=def_
    require(len(tile)==p*q*r and len(patch)==d*e*f,'array size')
    require(all(0<=a<=5 for a in tile),'tile digit domain')
    require(all(0<=a<=15 for a in patch),'patch digit domain')
    L=max(p*q*r+1,d*e*f+1) if L is None else L
    b=32**L;cap=b//16-1
    require(all(0<=v<=cap for v in U.values()),'supersolution cap')
    tx=max(2,(q*r+1+2*d-1)//(2*d),(e*f+1+2*p-1)//(2*p))
    ty=max(2,(r+1+2*e-1)//(2*e),(f+1+2*q-1)//(2*q))
    tz=2
    while any(not(-p*d*tx+1<=v[0]<=p*d*tx-2) for v,n in U.items() if n):tx+=1
    while any(not(-q*e*ty+1<=v[1]<=q*e*ty-2) for v,n in U.items() if n):ty+=1
    while any(not(-r*f*tz+1<=v[2]<=r*f*tz-2) for v,n in U.items() if n):tz+=1
    hx,hy,hz=p*d*tx,q*e*ty,r*f*tz
    A,B,C=2*hx,2*hy,2*hz;N=A*B*C
    T,D=pack(tile,32),pack(patch,32)
    Tb,Db=spread(T,32,p*q*r,L),spread(D,32,d*e*f,L)
    require(Tb==pack(tile,b) and Db==pack(patch,b),'precision conversions')
    tile_row=b**p;tile_plane=b**(A*q)
    tile_embed=spread(spread(Tb,tile_row,q*r,2*d*tx),tile_plane,r,2*e*ty)
    background=tile_embed*G(tile_row,2*d*tx)*G(tile_plane,2*e*ty)*G(b**(A*B*r),2*f*tz)
    patch_embed=spread(spread(Db,b**d,e*f,2*p*tx),b**(A*e),f,2*q*ty)
    additions=patch_embed*b**(hx+A*hy+A*B*hz)
    X,Y,Q=b**A,b**(A*B),b**N
    J=G(b,N)
    jx,jy,jz=G(b,A-2),G(X,B-2),G(Y,C-2)
    I=b*X*Y*jx*jy*jz
    require(b*b*((b-1)*jx+1)==X,'jx equation')
    require(X*X*((X-1)*jy+1)==Y,'jy equation')
    require(Y*Y*((Y-1)*jz+1)==Q,'jz equation')
    expectedH=expectedD=packedU=expectedI=0
    endpoints=[];maxleft=maxright=0
    for z,y,x in product(range(C),range(B),range(A)):
        index=x+A*y+A*B*z
        v=(x-hx,y-hy,z-hz)
        h=tile[(v[0]%p)+p*(v[1]%q)+p*q*(v[2]%r)]
        delta=patch[v[0]+d*v[1]+d*e*v[2]] if 0<=v[0]<d and 0<=v[1]<e and 0<=v[2]<f else 0
        u=U.get(v,0)
        incoming=sum(U.get(translate(v,direction),0) for direction in DIRECTIONS)
        end=h+delta-6*u+incoming
        require(0<=end<=5,'stable endpoint')
        power=b**index
        expectedH+=h*power;expectedD+=delta*power;packedU+=u*power
        if 0<x<A-1 and 0<y<B-1 and 0<z<C-1: expectedI+=power
        endpoints.append(end)
        maxleft=max(maxleft,h+delta+incoming);maxright=max(maxright,6*u+end)
    require(background==expectedH and additions==expectedD,'paid tensor geometry')
    require(I==expectedI,'interior mask')
    require(packedU & (cap*I)==packedU,'bounded interior mask')
    require(packedU%Y==0,'negative shifts integral')
    F=pack(endpoints,b)
    bits=[sum(((a>>k)&1)*b**j for j,a in enumerate(endpoints)) for k in range(3)]
    require(all(bit&J==bit for bit in bits),'endpoint bit masks')
    require((bits[1]+bits[2])&J==bits[1]+bits[2],'endpoint exclusion')
    require(F==bits[0]+2*bits[1]+4*bits[2],'endpoint reconstruction')
    neighbors=b*packedU+X*packedU+Y*packedU+packedU//b+packedU//X+packedU//Y
    require(background+additions+neighbors==6*packedU+F,'packed balance')
    require(maxleft<b and maxright<b,'observed carry bounds')
    # Direct boundary/exterior: every external vertex touched by U has no source.
    for v,n in U.items():
        if n:
            for direction in DIRECTIONS:
                w=translate(v,direction)
                require(-hx<=w[0]<hx and -hy<=w[1]<hy and -hz<=w[2]<hz,'exterior leakage')
    return dict(dimensions=[A,B,C],L=L,slots=N,max_odometer=max(U.values(),default=0),
                max_left_digit=maxleft,max_right_digit=maxright,
                raw_InputPlus=str(encode([p-1,q-1,r-1,T,d-1,e-1,f-1,D])))


def main():
    bounds=[]
    for L in range(1,41):
        b=32**L;c=b//16-1
        require(b//16==2**(5*L-4),'sixteenth binary width')
        require(20+6*c<b and 6*c+5<b,'universal no-carry bound')
        require(b-(20+6*c)==5*b//8-14,'left margin formula')
        bounds.append([L,b-(20+6*c),b-(6*c+5)])
    spread_cases=0
    for base in (2,4,8,32):
        for n in range(1,5):
            for stride in range(n+1,n+4):
                for j in range(30):
                    rng=random.Random(100000*base+1000*n+stride*30+j)
                    values=[rng.randrange(base) for _ in range(n)]
                    require(spread(pack(values,base),base,n,stride)==sum(a*base**(stride*i) for i,a in enumerate(values)),'spread regression')
                    spread_cases+=1
    fixtures={}
    for name,pdims,patch in (
            ('stable_zero',(1,1,1),[0]),
            ('single_repeated_origin',(1,1,1),[12]),
            ('two_site_repeated_prefix',(2,1,1),[12,4]),
            ('asymmetric_patch',(2,2,1),[15,7,10,3])):
        d,e,f=pdims
        initial={(x,y,z):patch[x+d*y+d*e*z] for z,y,x in product(range(f),range(e),range(d))}
        counts,endpoint,trace=stabilize(initial)
        fixtures[name]=fixture((1,1,1),pdims,[0],patch,counts)
        fixtures[name]['legal_topplings']=len(trace)
        require(all(n<6 for n in endpoint.values()),'legal endpoint')
        if name=='single_repeated_origin':require(counts[(0,0,0)]==2,'binary separator')
    # Supplied stabilizing witness need not be the least legal odometer.
    stable_initial={(0,0,0):5,(1,0,0):5}
    counts,_,trace=stabilize(stable_initial)
    require(not trace and not counts,'stable configuration true odometer')
    fixtures['nonleast_supersolution']=fixture((1,1,1),(2,1,1),[0],[5,5],{(0,0,0):1,(1,0,0):1})
    fixtures['nonleast_supersolution']['true_total_topplings']=0
    # Nonconstant periodic tile exercises all phase and repetition coordinates.
    fixtures['nonconstant_stable_tile']=fixture((2,2,2),(1,1,1),[0,1,2,3,4,5,0,5],[0],{})
    # Capacity/bitmask equivalence on single digits, including b=32 minimum.
    mask_tests=0
    for L in (1,2,3):
        b=32**L;c=b//16-1
        for value in range(min(b,5000)):
            require((value&c==value)==(value<=c),'digit capacity exactness')
            mask_tests+=1
    receipt=dict(status='PASS',spread_cases=spread_cases,capacity_digit_cases=mask_tests,
                 carry_bound_precisions=40,minimum_radix_margins=bounds[0],fixtures=fixtures,
                 checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 dag_sha256=hashlib.sha256((ROOT/'evidence/polynomial-dag.json').read_bytes()).hexdigest(),
                 scope='Finite semantic fixtures and bounds only; no complete expanded Pell witness, universal loader, or proof-by-enumeration claim.')
    (ROOT/'evidence/semantics-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
