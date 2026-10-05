"""Exact cycle-type, marked-leaf and Euler-transform checks through n=20.
The invariant-partition recurrence is reproduced from the preceding report;
its result is compared independently to the direct matrix census at n<=6.
"""
from fractions import Fraction
from math import factorial,gcd,comb
from collections import Counter
from pathlib import Path
import json

def parts(n,lo=1):
    if n==0:yield ();return
    for k in range(lo,n+1):
        for rest in parts(n-k,k):yield (k,)+rest

def bell_numbers(N):
    b=[1]
    for n in range(N):b.append(sum(comb(n,k)*b[k] for k in range(n+1)))
    return b

def invariant_count(lens,bell):
    nontrivial=[x for x in lens if x>1]
    r=len(nontrivial);c=len(lens);size=1<<r
    weight=[0]*size;card=[0]*size
    for mask in range(1,size):
        v=mask&-mask;i=v.bit_length()-1;rest=mask^v
        card[mask]=card[rest]+1
        common=0
        for j,l in enumerate(nontrivial):
            if mask>>j&1:common=gcd(common,l)
        weight[mask]=sum(d**(card[mask]-1) for d in range(2,common+1) if common%d==0)
    E=[0]*size;E[0]=1
    for mask in range(1,size):
        first=mask&-mask;rest=mask^first;sub=rest
        while True:
            block=sub|first
            E[mask]+=weight[block]*E[mask^block]
            if sub==0:break
            sub=(sub-1)&rest
    return sum(E[mask]*bell[c-card[mask]] for mask in range(size))

N=20;B=bell_numbers(N+1)
expected_A=[1,1,4,10,33,91,298,910,3017,9945,34207,119369,429250,1574224,5916148,22699830,89003059,356058540,1453080087,6044132794,25612598436]
expected_C=[0,1,3,6,17,40,125,354,1159,3774,13113,46426,171027,644038,2493848,9867688,39922991,164747459,693093407,2968918400,12940917244]
A=[];Z=[];Y=[];L=[];types=0
for n in range(N+1):
    aa=Fraction();zz=Fraction();yy=Fraction();ll=Fraction()
    for lens in parts(n):
        mult=Counter(lens);den=1;c=len(lens)
        for i,m in mult.items():den*=i**m*factorial(m)
        f=invariant_count(lens,B)
        aa+=Fraction(f*f,den);zz+=Fraction(B[c]**2,den)
        yy+=Fraction(B[c]*B[c+1],den)
        if mult[2]:ll+=Fraction(2*mult[2]*B[c]*B[c-1],den)
        types+=1
    assert aa.denominator==1 and aa==expected_A[n]
    A.append(int(aa));Z.append(zz);Y.append(yy);L.append(ll)
    if n>=2:assert ll==Y[n-2]
    assert aa-zz-ll>=0
C=[0]*(N+1);g=[0]*(N+1);b=[1]
for n in range(1,N+1):
    g[n]=n*A[n]-sum(g[k]*A[n-k] for k in range(1,n))
    numerator=g[n]-sum(d*C[d] for d in range(1,n) if n%d==0)
    assert numerator%n==0
    C[n]=numerator//n
    b.append(-sum(A[k]*b[n-k] for k in range(1,n+1)))
assert C==expected_C
assert b[:7]==[1,-1,-3,-3,-8,-8,-38]
# Reconstruct A by the multiset/Euler product.
prod=[1]+[0]*N
for m in range(1,N+1):
    q=[0]*(N+1);q[0]=1
    for r in range(1,N//m+1):q[r*m]=comb(C[m]+r-1,r)
    prod=[sum(prod[j]*q[n-j] for j in range(n+1)) for n in range(N+1)]
assert prod==A
census_path=Path(__file__).with_name('check_graphs.json')
if not census_path.exists():raise RuntimeError('Run check_graphs.py first')
for row in json.loads(census_path.read_text())['rows']:
    n=row['n']
    assert row['graphs']==A[n] and row['connected']==C[n]
    assert Fraction(row['weighted_mass'])==Z[n]
    assert Fraction(row['leaf_weight'])==L[n]
    assert Fraction(row['Y'])==Y[n]
rows=[dict(n=n,a=A[n],connected=C[n],Z=str(Z[n]),Y=str(Y[n]),marked_leaf_mass=str(L[n]),b=b[n]) for n in range(N+1)]
result=dict(status='PASS',maximum_n=N,cycle_types=types,reciprocal_prefix=b[:7],rows=rows)
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS cycle types',types,'through n=',N,'; direct census cross-checks through n=6; Euler transform and reciprocal coefficients')
