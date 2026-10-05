"""Exact Bonferroni probability enclosures, independent of guessed recurrences."""
from fractions import Fraction
from math import factorial,prod,comb
from pathlib import Path
import json, decimal, sys
from compute_coefficients import parts

def ff(n,k):return prod(range(n-k+1,n+1))
def stable(n,r,weights):
    counts={d:weights.count(d) for d in set(weights)}
    c=len(weights);j=sum(weights)
    e=[1]
    for d in weights:
        new=e+[0]
        for h in range(1,len(new)):new[h]+=d*e[h-1]
        e=new
    ans=0;rise=1
    for h in range(c+1):
        if h:rise*=r+h-2
        ans+=(-1)**h*rise*e[h]*ff(n-j-h,c-h)
    den=prod(factorial(x) for x in counts.values())
    if ans%den:raise ValueError("Nonintegral profile")
    return ans//den,den

def enclosure(n,r,s,J):
    if min(n//r,n//s)<2*(J+1):raise ValueError("Outside stable regime")
    sums=Fraction(0);mom=[]
    for j in range(J+2):
        moment=Fraction(0)
        for weights in parts(j):
            cr,den=stable(n,r,weights);cs,_=stable(n,s,weights)
            moment+=Fraction(cr*cs*den,ff(n,j+len(weights)))
        sums+=(-1)**j*moment
        if j>=J:mom.append(sums)
    return min(mom),max(mom)

decimal.getcontext().prec=70
D=decimal.Decimal
coeff=[1,3,2,1,0,3,26,101,124,-1409,-13266]
records=[]
for n,J in [(100,23),(200,27),(1000,29)]:
    lo,hi=enclosure(n,2,2,J)
    def dec(q):return D(q.numerator)/D(q.denominator)
    el,eh=dec(lo)*D(1).exp(),dec(hi)*D(1).exp()
    model=sum(D(c)/D(n)**i for i,c in enumerate(coeff))
    records.append({"n":n,"J":J,"probability_interval":[str(lo),str(hi)],
                    "e_times_probability":[str(el),str(eh)],
                    "scaled_order11_residual":[str((el-model)*D(n)**11),
                                               str((eh-model)*D(n)**11)]})
Path(__file__).with_suffix(".json").write_text(json.dumps(records,indent=2)+"\n")
for rec in records:print({k:rec[k] for k in ["n","J","e_times_probability","scaled_order11_residual"]})
