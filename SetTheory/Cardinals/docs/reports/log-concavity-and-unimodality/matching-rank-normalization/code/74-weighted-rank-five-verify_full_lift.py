"""Independent exact audit of the full rank-five two-coordinate matroid lift."""
from itertools import combinations
from fractions import Fraction
from math import prod
from random import Random
from pathlib import Path
import json

def det_mod(columns,p):
    n=len(columns);A=[[columns[j][i]%p for j in range(n)]for i in range(n)]
    det=1
    for i in range(n):
        pivot=next((j for j in range(i,n)if A[j][i]),None)
        if pivot is None:return 0
        if pivot!=i:A[i],A[pivot]=A[pivot],A[i];det=-det
        aa=A[i][i];det=det*aa%p;inv=pow(aa,p-2,p)
        for j in range(i+1,n):
            fac=A[j][i]*inv%p
            for k in range(i+1,n):A[j][k]=(A[j][k]-fac*A[i][k])%p
    return det%p

def support_counts(adj,u,v):
    n=len(v);wp=[1]*(1<<n)
    for J in range(1,1<<n):
        bit=J&-J;wp[J]=wp[J-bit]*v[bit.bit_length()-1]
    out=[0]*6
    for I in range(1<<len(u)):
        k=I.bit_count()
        if k>5:continue
        reach={0};ww=1
        for i in range(len(u)):
            if I>>i&1:
                ww*=u[i]
                reach={J|(1<<j)for J in reach for j in adj[i]if not J>>j&1}
                if not reach:break
        out[k]+=ww*sum(wp[J]for J in reach)
    return out

rng=Random(635714);p=1000000007;records=[];total=0
for s1 in range(8):
 for s2 in range(8):
    n=rng.randrange(3,6);L=[rng.randrange(1,8)for _ in range(n)]
    ul=[rng.randrange(1,7)for _ in L];v=[rng.randrange(1,7)for _ in range(3)]
    x,y=rng.randrange(1,7),rng.randrange(1,7)
    a,b=rng.randrange(6),rng.randrange(6)
    common=[rng.randrange(1,7)for _ in range(rng.randrange(4))]
    c=sum(common);d=sum(i*j for i,j in combinations(common,2));q=a*b+a*c+b*c+d
    if q==0:a=b=1;q=a*b+a*c+b*c+d
    def vec(mask):return [rng.randrange(1,p)if mask>>j&1 else 0 for j in range(3)]
    # Private right-core coordinates, exterior-left columns, two core-left columns.
    vectors=[[int(i==j)for j in range(5)]for i in range(3)]
    vectors += [vec(t)+[0,0]for t in L]
    vectors += [vec(s1)+[1,0],vec(s2)+[0,1]]
    # The plane frame has the swapped activities b/q,a/q.
    vectors += [[0,0,0,1,0],[0,0,0,0,1]]
    vectors += [[0,0,0,rng.randrange(1,p),rng.randrange(1,p)]for _ in common]
    weights=[Fraction(1,w)for w in v]+list(map(Fraction,ul))+[Fraction(x),Fraction(y),Fraction(b,q),Fraction(a,q)]+[Fraction(w,q)for w in common]
    left_indices=set(range(3,3+n+2));model=[Fraction(0)]*6
    for basis in combinations(range(len(vectors)),5):
        total+=1
        if det_mod([vectors[i]for i in basis],p):
            k=len(set(basis)&left_indices)
            model[k]+=prod(weights[i]for i in basis)*q*prod(v)
    rtypes=[1,2]+[3]*len(common);right=v+[a,b]+common
    adj=[{j for j in range(3)if s1>>j&1}|{3+j for j,t in enumerate(rtypes)if t&1},
         {j for j in range(3)if s2>>j&1}|{3+j for j,t in enumerate(rtypes)if t&2}]
    adj += [{j for j in range(3)if mask>>j&1}for mask in L]
    actual=support_counts(adj,[x,y]+ul,right)
    assert list(model)==actual,(s1,s2,L,model,actual)
    assert all(k*(5-k)*actual[k]**2>=(k+1)*(6-k)*actual[k-1]*actual[k+1]for k in range(1,5))
    records.append({'core':s1|(s2<<3),'left_types':L,'common_right_count':len(common),'coefficients':actual})
out={'seed':635714,'prime':p,'graphs':len(records),'finite_field_basis_tests':total,
 'full_lift_identity':True,'all_ULC5_checks':True,'records':records,
 'scope':'Finite exact checks; the generic determinant expansion is the universal proof.'}
(Path(__file__).resolve().parents[1]/'data'/'full_lift_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='records'}))
