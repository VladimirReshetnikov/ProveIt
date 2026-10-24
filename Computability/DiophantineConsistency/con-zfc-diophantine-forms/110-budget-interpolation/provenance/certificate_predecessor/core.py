"""Exact packed-convolution tiling certificate; no external dependencies.

The binomial parity evaluator is Lucas' exact binary algorithm. It does not
pretend that the uncomputed, usually enormous full binomial is a polynomial.
"""
from dataclasses import dataclass
from math import comb

@dataclass(frozen=True)
class Tile:
    west: int
    east: int
    north: int
    south: int

def constants(tiles):
    if not tiles or any(min(t.west,t.east,t.north,t.south)<0 for t in tiles):
        raise ValueError('A nonempty tile set with natural edge colors is required')
    k=len(tiles); C=1
    while C<=max(k,max(max(t.west,t.east,t.north,t.south) for t in tiles)):
        C*=2
    A0=2*C*C; D=1
    while D<32*k*A0: D*=2
    return C,A0,D

def rows(tiles,Q,P,G,C):
    coeff=[[],[],[],[],[],[],[]]
    for t in tiles:
        vals=(1,(Q-1)*int(t.west==0),C*int(t.east==0)-Q*int(t.west==0),
              C*t.east-t.west,Q*t.south-t.north,
              (C-1)*int(t.north==0),Q*int(t.south==0)-P*int(t.north==0))
        for row,v in zip(coeff,vals): row.append(v)
    return coeff,[-G,-(P-1),0,0,0,-(Q-1),0]

def geometry(tiles,w,h):
    if w<1 or h<1: raise ValueError('Dimensions must be positive')
    C,A0,D=constants(tiles); Q=C**w; P=Q**h; G=(P-1)//(C-1)
    return {'C':C,'A0':A0,'D':D,'Q':Q,'P':P,'G':G,'H':A0*P,'R':D*P**3}

def pack_masks(tiles,w,h,masks):
    g=geometry(tiles,w,h)
    if len(masks)!=len(tiles) or min(masks)<0: raise ValueError('Invalid masks')
    return sum(v*g['R']**i for i,v in enumerate(masks))

def board_masks(tiles,w,h,board):
    if len(board)!=w*h: raise ValueError('Board length differs from its area')
    C,_,_=constants(tiles)
    return [sum(C**i for i,t in enumerate(board) if t==j) for j in range(len(tiles))]

def data(tiles,w,h,Z):
    if Z<0: raise ValueError('Z is natural')
    d=geometry(tiles,w,h); k=len(tiles)
    C,Q,P,G,H,R=[d[n] for n in ('C','Q','P','G','H','R')]
    B=R//2; L=R**(2*k)
    aa,cc=rows(tiles,Q,P,G,C)
    K=[sum((H+a)*R**(k-1-t) for t,a in enumerate(row)) for row in aa]
    F=[v*Z+(B-H*G+c)*R**(k-1) for v,c in zip(K,cc)]
    M0=G*sum(R**t for t in range(k))
    M1=R**(2*k-1)-1-(R-1-B)*R**(k-1)
    A=M0+M1*sum(L**j for j in range(1,8))
    Y=Z+sum(v*L**j for j,v in enumerate(F,1))
    d.update(B=B,L=L,Z=Z,K=K,F=F,M0=M0,M1=M1,A=A,Y=Y,coeff=aa,const=cc)
    return d

def lucas_odd(A,Y):
    if min(A,Y)<0: raise ValueError('Natural binomial inputs required')
    return (Y & ~A)==0

def global_test(tiles,w,h,Z):
    d=data(tiles,w,h,Z)
    return lucas_odd(d['A'],d['Y'])

def direct_board_test(tiles,w,h,board):
    if len(board)!=w*h or any(i<0 or i>=len(tiles) for i in board): return False
    for j,idx in enumerate(board):
        t=tiles[idx]; row,col=divmod(j,w)
        if (t.west==0)!=(col==0) or (t.east==0)!=(col==w-1): return False
        if (t.north==0)!=(row==0) or (t.south==0)!=(row==h-1): return False
        if col+1<w and t.east!=tiles[board[j+1]].west: return False
        if row+1<h and t.south!=tiles[board[j+w]].north: return False
    return True

def decoded_mask_test(tiles,w,h,Z):
    d=geometry(tiles,w,h); C,R,G=d['C'],d['R'],d['G']; k=len(tiles)
    masks=[]; z=Z
    for _ in range(k): masks.append(z%R); z//=R
    if z or sum(masks)!=G or any(x & ~G for x in masks): return False
    board=[]
    for i in range(w*h):
        at=[t for t,x in enumerate(masks) if (x//(C**i))%C]
        if len(at)!=1: return False
        board.append(at[0])
    return direct_board_test(tiles,w,h,board)

def power_only_witness(A,Y):
    """For SMALL inputs only: construct the parity-elimination witnesses."""
    if min(A,Y)<0: raise ValueError('Natural inputs required')
    d=2**(A+1); e=2**((A+1)*Y)
    quotient,s=divmod((d+1)**A,e)
    if quotient%2==0: return None
    return d,(quotient-1)//2,s,e-s-1

def power_only_test(A,Y,witness):
    if witness is None: return False
    d,q,s,t=witness
    return min(witness)>=0 and d==2**(A+1) and s+t+1==2**((A+1)*Y) and (s+t+1)*(2*q+1)+s==(d+1)**A

CORNERS=[Tile(0,1,0,2),Tile(1,0,0,3),Tile(0,4,2,0),Tile(4,0,3,0)]
