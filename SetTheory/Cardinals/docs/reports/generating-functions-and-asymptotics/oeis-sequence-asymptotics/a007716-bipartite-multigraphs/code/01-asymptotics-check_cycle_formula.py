"""Exact independent cycle-type reconstruction of A007716 and its weighted mass."""
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

N=20;b=bell_numbers(N)
expected=[1,1,4,10,33,91,298,910,3017,9945,34207,119369,429250,1574224,5916148,22699830,89003059,356058540,1453080087,6044132794,25612598436]
rows=[];types=0
for n in range(N+1):
    a=Fraction(0);mass=Fraction(0)
    for lens in parts(n):
        mult=Counter(lens);z=1
        for l,m in mult.items():z*=l**m*factorial(m)
        f=invariant_count(lens,b);c=len(lens);d=n-c
        if not b[c]<=f<=2**d*b[c]:raise RuntimeError(('bound',lens,f,b[c]))
        a+=Fraction(f*f,z);mass+=Fraction(b[c]*b[c],z);types+=1
    if a.denominator!=1 or a.numerator!=expected[n]:raise RuntimeError(('OEIS mismatch',n,a,expected[n]))
    rows.append({'n':n,'a':a.numerator,'mass_numerator':mass.numerator,'mass_denominator':mass.denominator,'a_over_mass':str(a/mass)})
result={'status':'PASS','maximum_n':N,'cycle_types_checked':types,'rows':rows,'method':'Independent subset recurrence for nontrivial block-orbits and exact Burnside cycle-type sum; no imported root checker.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',N,types)
