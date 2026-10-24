#!/usr/bin/env python3
"""Regression tests. Universal correctness is proved in PROOF.md, not inferred here."""
from core import *
from itertools import product
from collections import Counter
from pathlib import Path
import json,random
COUNTS=Counter()
def require(v,msg):
    if not v: raise RuntimeError(msg)
def test_free(tiles,G,Q,Z):
    shape=geometric_power_test(tiles,G,Q)
    want=bool(shape) and decoded_mask_test(tiles,*shape,Z)
    got=free_test(tiles,G,Q,Z)
    require(got==want,f'Free geometry mismatch G={G},Q={Q},Z={Z},shape={shape}')
    COUNTS['free_geometry_cases']+=1
    if got:
        d=data_free(tiles,G,Q,Z)
        require(Q<2*d['P'] and Z<d['L'],'Bootstrap bound failed')
        require(d['A']>=d['P'] and d['A']>=10,'Completeness size bound failed')
        require(all(0<=f<d['L'] for f in d['F']),'Lane overflow')
        COUNTS['accepted_free_geometry_cases']+=1

for A in range(100):
    for Y in range(104):
        require(lucas_odd(A,Y)==(Y<=A and comb(A,Y)%2==1),'Lucas parity')
        COUNTS['literal_binomial_cases']+=1

# Exact divisibility synchronization lemma, independent of tilings.
for n in range(1,85):
    P=2**n
    for q in range(2,401):
        got=P%q==0 and (P-1)%(q-1)==0
        u=q.bit_length()-1
        want=(q==2**u and n%u==0)
        require(got==want,'Power synchronization failed')
        COUNTS['elementary_synchronization_cases']+=1

# Deliberately non-geometric Q; no range hypothesis is supplied to the formula.
T=[Tile(0,0,0,0),Tile(0,1,0,0)]
for N in [1,2,3]:
    C,_,_=constants(T); P=C**N; G=(P-1)//(C-1)
    R=constants(T)[2]*P**3
    masks=list(product(range(G+3),repeat=2))
    for Q in list(range(0,2*P+5))+[R,R**2,R**4]:
        for xx in masks:
            Z=sum(x*R**i for i,x in enumerate(xx))
            test_free(T,G,Q,Z)

# Exhaustive small genuine-board test; arbitrary Q is also sampled at each area.
for w,h in [(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)]:
    g=geometry(CORNERS,w,h)
    for board in product(range(4),repeat=w*h):
        Z=pack_masks(CORNERS,w,h,board_masks(CORNERS,w,h,board))
        require(global_test(CORNERS,w,h,Z)==direct_board_test(CORNERS,w,h,board),'Board mismatch')
        COUNTS['exhaustive_corner_boards']+=1
        if direct_board_test(CORNERS,w,h,board): test_free(CORNERS,g['G'],g['Q'],Z)

rng=random.Random(20261024)
for _ in range(1600):
    k=rng.randrange(1,7);tiles=[Tile(*(rng.randrange(4) for _ in range(4))) for j in range(k)]
    N=rng.randrange(1,7);C,_,D=constants(tiles);P=C**N;G=(P-1)//(C-1);R=D*P**3
    Q=rng.choice([rng.randrange(2*P+10),C**rng.randrange(1,N+3),R**rng.randrange(1,5)])
    Z=sum(rng.randrange(2*G+5)*R**i for i in range(k))
    if rng.randrange(3)==0:Z+=R**(k+rng.randrange(4))
    test_free(tiles,G,Q,Z)

# Positive nonsquare rectangles constructed with unique internal edge colors.
for w,h in [(1,1),(1,2),(2,1),(1,3),(3,1),(2,3),(3,2),(2,4),(4,2)]:
    tiles=[];base=1+h*max(w-1,0)
    for row in range(h):
        for col in range(w):
            west=0 if col==0 else 1+row*(w-1)+col-1
            east=0 if col==w-1 else 1+row*(w-1)+col
            north=0 if row==0 else base+(row-1)*w+col
            south=0 if row==h-1 else base+row*w+col
            tiles.append(Tile(west,east,north,south))
    board=list(range(w*h));g=geometry(tiles,w,h)
    Z=pack_masks(tiles,w,h,board_masks(tiles,w,h,board))
    require(direct_board_test(tiles,w,h,board),'Constructed rectangle invalid')
    test_free(tiles,g['G'],g['Q'],Z)
    COUNTS['constructed_positive_rectangles']+=1

# Second-order synchronization, including arbitrary nonpowers for d.
# e=2^n, d>n, d|e, and (e-1)/(d-1) = Y mod d-1 force e=d^Y.
for n in range(1,70):
    e=2**n
    ds=set(range(n+1,n+35))|{2**u for u in range(1,min(n,12)+1)}
    for d in ds:
        for Y in range(1,n+1):
            if d<=n: continue
            got=e%d==0 and (e-1)%(d-1)==0 and ((e-1)//(d-1)-Y)%(d-1)==0
            require(got==(d**Y==e),'Second-order synchronization failed')
            COUNTS['second_order_synchronization_cases']+=1

# Kernel of the 8-coordinate/2-graph interface, at manageable literal sizes.
# Its huge tiling A values are intentionally not exponentiated in this test.
for A in range(10,31):
    for Y in range(1,A+3):
        for P in [2,4,8,16]:
            if P>A: continue
            d=2**(A+1); n=(A+1)*Y
            v=d//P-n-1
            if v<0: continue
            e=2**n; value=(d+1)**A; quotient,s=divmod(value,e)
            want=(Y<=A and comb(A,Y)%2==1)
            if not want:
                require(quotient%2==0,'Invalid parity unexpectedly odd')
            else:
                q=(quotient-1)//2;u=(s-1)//d;t=e//d-u-1
                j=((e-1)//(d-1)-Y)//(d-1)
                require(min(v,q,u,t,j)>=0,'Negative completeness coordinate')
                require(d==P*(n+v+1),'Large-base substitution failed')
                require(e==d*(u+t+1),'Divisibility/remainder parametrization failed')
                require(e-1==(d-1)*(Y+(d-1)*j),'Second-order residual failed')
                require(value==e*(2*q+1)+d*u+1,'Parity residual failed')
                COUNTS['two_graph_kernel_positive_cases']+=1
            COUNTS['two_graph_kernel_cases']+=1

# Omitting the size guard admits a false exponent congruence.
# e=8,d=2,Y=1 gives h=3, but modulo d-1=1 every Y passes.
require(8%2==0 and (8-1)==(2-1)*(1+(2-1)*6) and 2**1!=8,'Missing-bound counterexample')
COUNTS['essential_guard_counterexamples']+=1
out={'status':'passed','optimized_mode':not __debug__,'counts':dict(COUNTS),
     'ordinary_polynomial_claim':False,
     'interfaces':{'one_power_one_binomial':'5+p_2+b','three_powers':'7+2*p_2+p_g','two_powers':'8+p_2+p_g'},
     'note':'Internal graph witnesses are not implemented or silently excluded. See the universal proofs and graph contracts.'}
Path(__file__).with_name('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
