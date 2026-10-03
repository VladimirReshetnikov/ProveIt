"""Exact all-unit witness verification by support deficits and pendant factors."""
from math import comb,prod,gcd
from fractions import Fraction
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]/"data"

def binom(n,k):return comb(n,k) if 0<=k<=n else 0

def top_deficit(a,b,N,M,W,delta):
    K=M*(W-1)
    total=0
    for olddef in range(delta+1):
        missing=delta-olddef
        for u in range(olddef+1):
            for v in range(olddef-u+1):
                i,j=a-u,b-v
                l=b-olddef+u;rho=a-olddef+v
                multiplicity=binom(a,u)*binom(b,v)*binom(N,l)*binom(M,rho)
                A=K-M+rho;B=M-rho
                # Exactly 'missing' of the K linear gadget factors contribute1.
                gadget=sum(binom(A,missing-z)*binom(B,z)*W**(B-z)
                           for z in range(missing+1)if B-z>=0)
                total+=multiplicity*gadget
    return total

def verify(a,b,N,M,W,name):
    r=a+b;K=M*(W-1);R=r+K
    pR,pR1,pR2=[top_deficit(a,b,N,M,W,j)for j in range(3)]
    margin=(R-1)*pR1*pR1-2*R*pR2*pR
    assert margin<0
    # Independent normalized formula from reciprocal sums of the gadget factors.
    h=N-b+1;tt=Fraction(b,h);zz=Fraction(b*(b-1),h*(h+1))
    uu=Fraction(a,M-a+1);vv=Fraction(a*(a-1),(M-a+1)*(M-a+2))
    LL=K-M+a+Fraction(M-a,W);SS=K-M+a+Fraction(M-a,W*W)
    first=LL+W*uu*(a+tt)+b*tt
    second=(LL*LL-SS)/2+W*uu*(a+tt)*(LL-1+Fraction(1,W))+b*tt*LL+W*W*vv*(comb(a,2)+a*tt+zz)+W*b*uu*(zz+a*tt)+comb(b,2)*zz
    assert Fraction(pR1,pR)==first and Fraction(pR2,pR)==second
    # Explicit matching and cover checks without storing a huge edge list.
    left=[('A',i)for i in range(a)]+[('L',i)for i in range(N)]+[('Z',j,h)for j in range(M)for h in range(W-1)]
    right=[('B',j)for j in range(b)]+[('R',j)for j in range(M)]+[('P',j,h)for j in range(M)for h in range(W-1)]
    matching=[(('A',i),('R',i))for i in range(a)]+[(('L',j),('B',j))for j in range(b)]
    matching += [(('Z',j,h),('P',j,h))for j in range(M)for h in range(W-1)]
    cover=set([('A',i)for i in range(a)]+[('B',j)for j in range(b)]+[('Z',j,h)for j in range(M)for h in range(W-1)])
    assert len(matching)==R==len(cover)
    assert len(set(x for x,y in matching))==R==len(set(y for x,y in matching))
    def edges():
        for i in range(a):
            for j in range(b):yield ('A',i),('B',j)
            for j in range(M):yield ('A',i),('R',j)
        for i in range(N):
            for j in range(b):yield ('L',i),('B',j)
        for j in range(M):
            for h in range(W-1):
                yield ('Z',j,h),('R',j)
                yield ('Z',j,h),('P',j,h)
    count=0
    for x,y in edges():
        assert x in cover or y in cover
        count+=1
    assert count==a*b+a*M+b*N+2*K
    C0=comb(N,b)*comb(M,a)
    exponent=M-a
    scaled=[Fraction(pR,W**exponent),Fraction(pR1,W**(exponent-1)),Fraction(pR2,W**(exponent-2))]
    assert all(x.denominator==1 for x in scaled)
    normalized_margin=Fraction(margin,W**(2*exponent-2))
    assert normalized_margin.denominator==1
    rec={'parameters':{'a':a,'b':b,'N':N,'M':M,'arms_per_exterior_right_vertex':W-1},
      'all_vertex_activities':1,'matching_rank':R,'left_vertices':len(left),'right_vertices':len(right),
      'vertices':len(left)+len(right),'edges':count,'smaller_shore_deficiency':min(len(left),len(right))-R,
      'tail_coefficients_r_rminus1_rminus2':list(map(str,(pR,pR1,pR2))),
      'tail_factors':{'base':W,'exponents':[exponent,exponent-1,exponent-2],'integer_multipliers':list(map(lambda x:str(x.numerator),scaled))},
      'endpoint_gap':str(margin),'endpoint_gap_factor':{'integer':str(normalized_margin.numerator),'base':W,'exponent':2*exponent-2},
      'matching_and_cover_verified':True,'exact_deficit_count_matches_normalized_formula':True}
    (ROOT/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    return rec

if __name__=='__main__':
    verify(12,398,410,16,191,'unit_rank3450_witness')
    verify(8,100,101,30,4181,'unit_deficiency_one_witness')
