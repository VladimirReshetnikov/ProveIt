"""Independent exact combinatorial and Jordan-sector checks (no fitting)."""
from fractions import Fraction
from math import comb, factorial
from itertools import product, permutations
from pathlib import Path
import json


def counts(k,N):
    A=[0]*(N+1); L=[0]*(N+1)
    for n in range(1,N+1):
        A[n]=n**(k*n)-sum(comb(n,h)*n**(k*(n-h))*A[h] for h in range(1,n))
        L[n]=A[n]+sum(comb(n-1,j)*A[j]*L[n-j] for j in range(1,n))
    return A,L

def stirling(m,n):
    row=[1]+[0]*n
    for _ in range(m):
        row=[0]+[j*row[j]+row[j-1] for j in range(1,n+1)]
    return row[n]

def R(k,h,r):
    # Complete homogeneous symmetric polynomial h_((k-1)r)(h,...,h+r)
    D=(k-1)*r
    coeff=[1]+[0]*D
    for x in range(h,h+r+1):
        for j in range(1,D+1): coeff[j]+=x*coeff[j-1]
    return coeff[D]

def jordan(a,l):
    ans=l**a;p=2;x=l
    while p*p<=x:
        if x%p==0:
            ans=ans//(p**a)*(p**a-1)
            while x%p==0:x//=p
        p+=1
    if x>1:ans=ans//(x**a)*(x**a-1)
    return ans

def unrooted(k,n,L,color=1):
    return sum(Fraction(L[n//ell],factorial(n//ell)*ell)*jordan((k-1)*(n//ell)+1,ell)*color**(n//ell)
               for ell in range(1,n+1) if n%ell==0)

def strict_rgs(k,n):
    count=0
    def rec(w,maximum):
        nonlocal count
        if len(w)==k*n:
            count+=maximum==n-1; return
        for x in range(min(maximum+1,n-1)+1):
            w1=w+(x,);max1=max(maximum,x)
            if len(w1)%k==0 and len(w1)<k*n and max1+1<len(w1)//k+1:continue
            rec(w1,max1)
    rec((0,),0)
    return count

def brute(k,n,color=1):
    per=list(permutations(range(n))); classes=set(); labeled=0
    for f in product(range(n),repeat=k*n):
        strong=True
        for root in range(n):
            seen={root};stack=[root]
            while stack:
                u=stack.pop()
                for v in f[k*u:k*(u+1)]:
                    if v not in seen:seen.add(v);stack.append(v)
            if len(seen)<n:strong=False;break
        if not strong:continue
        labeled+=1
        for colors in product(range(color),repeat=n):
            reps=[]
            for p in per:
                mapped=[0]*(k*n);newcolors=[0]*n
                for u in range(n):
                    newcolors[p[u]]=colors[u]
                    for a in range(k):mapped[k*p[u]+a]=p[f[k*u+a]]
                reps.append(tuple(mapped)+tuple(newcolors))
            classes.add(min(reps))
    return labeled,len(classes)

out={'checks':[], 'sector_examples':[]}
for k in range(2,6):
    A,L=counts(k,35)
    for n in range(1,18):
        P=Fraction(A[n],factorial(n));assert P.denominator==1
        rhs=P+sum(Fraction(A[h],factorial(h))*R(k,h,n-h) for h in range(1,n))
        assert rhs==stirling(k*n,n)
        U=unrooted(k,n,L);assert U.denominator==1
        if n in [2,3,5,7,11,13,17]:
            assert U-Fraction(L[n],factorial(n))==Fraction(jordan(k,n),n)
    out['checks'].append({'k':k,'strict_renewal_n':17,'unrooted_integrality_n':17})
for k,n in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)]:
    A,L=counts(k,n)
    if k*n<=9:assert strict_rgs(k,n)==A[n]//factorial(n)
    actual=brute(k,n)
    assert actual==(L[n],unrooted(k,n,L))
    out['checks'].append({'k':k,'n':n,'brute_labeled':actual[0],'brute_unrooted':actual[1]})
for k,n in [(2,2),(2,3),(3,2)]:
    A,L=counts(k,n);actual=brute(k,n,color=2)[1]
    assert actual==unrooted(k,n,L,color=2)
    out['checks'].append({'k':k,'n':n,'brute_terminal_subset_classes':actual})
# One-letter cycle sanity: B_m=1/m and rank-one Jordan phi.
for n in range(1,51):
    U=sum(Fraction(jordan(1,ell),n) for ell in range(1,n+1) if n%ell==0)
    assert U==1
out['checks'].append({'k':1,'cycle_identity_n':50})
for n in [6,8,9,10,11,12,15,16,18,20,24,30]:
    _,L=counts(2,n);terms={str(ell):str(Fraction(L[n//ell],factorial(n//ell)*ell)*jordan(n//ell+1,ell))
         for ell in range(1,n+1) if n%ell==0}
    out['sector_examples'].append({'n':n,'exact_sectors':terms,'sum':str(unrooted(2,n,L))})
Path(__file__).with_name('exact_sector_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print('All exact renewal, brute strong/isomorphism, terminal-subset, Jordan, and prime-sector checks passed.')
