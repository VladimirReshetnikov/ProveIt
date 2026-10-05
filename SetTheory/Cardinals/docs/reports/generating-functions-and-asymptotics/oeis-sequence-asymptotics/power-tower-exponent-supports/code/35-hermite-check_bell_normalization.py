"""Independent exact derivative recurrence versus the fixed-defect Bell formula.
Uses rational truncated products, not the author's logarithmic recurrence.
"""
from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import json
NMAX,RMAX=50,10

def mul(a,b):
    return [sum((a[j]*b[i-j] for j in range(i+1)),F(0)) for i in range(RMAX+1)]

sq=[F(1)]
for j in range(1,RMAX+2):sq.append(sq[-1]*(F(1,2)-j+1)/j)
lg=[F(0)]+[F((-1)**(j+1),j) for j in range(1,RMAX+2)]
A=[sum((sq[i]*lg[j+1-i] for i in range(j+1)),F(0)) for j in range(RMAX+1)]
B=[2*sq[j+1] for j in range(RMAX+1)]
one=[F(1)]+[F(0)]*RMAX
AP=[one];BP=[one]
for n in range(1,NMAX+1):
    AP.append(mul(AP[-1],A));BP.append(mul(BP[-1],B))
# q_{N,ell,k}=2^N p_{N,ell,k}(1/2), all integer.
row={(0,0):1};checks=0
for N in range(1,NMAX+1):
    new={}
    def add(ell,k,value):
        if value:new[ell,k]=new.get((ell,k),0)+value
    for (ell,k),value in row.items():
        add(ell,k,(ell-2*(N-1))*value)
        if k:add(ell,k-1,2*k*value)
        add(ell+1,k,2*value)
        add(ell+1,k+1,value)
    row={key:value for key,value in new.items() if value}
    for r in range(min(RMAX,N-1)+1):
        ell=N-r
        for k in range(ell+1):
            residual=sum((AP[ell-k][j]*BP[k][r-j] for j in range(r+1)),F(0))
            expected=2**(N-k)*factorial(N)//factorial(ell)*comb(ell,k)*residual
            actual=row.get((ell,k),0)
            if expected!=actual:raise RuntimeError((N,r,k,expected,actual))
            checks+=1
out={'max_order':NMAX,'max_defect':RMAX,'exact_coefficient_identities_checked':checks,'passed':True,'method':'integer differential recurrence versus direct rational A/B powers'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
