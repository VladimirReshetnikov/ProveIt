"""Exact symbolic verification of the diagonal-to-total transfer coefficients.

All formal calculations are exact. The network-word comparison is a finite
sanity check; the all-n identity is sourced to Lin et al. 2026, Theorem 1.1.
"""
import json
from fractions import Fraction
from math import factorial
from pathlib import Path
import sympy as s

ROOT=Path(__file__).resolve().parent
m,t,B=s.symbols('m t B')
L1,L2,L3=s.symbols('L1 L2 L3')
R=6
cut=lambda expr:s.series(expr,t,0,R+1).removeO().expand()
phi=cut(t*(1-t**3)**s.Rational(-1,3))
logQ=cut(s.log(1-(m+1)*t**3/3)-s.Rational(2,3)*s.log(1-t**3)+B/t*((1-t**3)**s.Rational(1,3)-1)+L1*(phi-t)+L2*(phi**2-t**2)+L3*(phi**3-t**3))
Q=cut(s.exp(logQ))
P={0:m+1}
for r in range(1,R+1):
    source=-s.expand(Q*sum(P[j].subs(m,m-1)*cut(phi**j) for j in range(r))).coeff(t,r)
    deg=0 if source==0 else s.degree(source,m)+2
    cc=s.symbols('c:'+str(deg+1))
    poly=sum(c*m**i for i,c in enumerate(cc))
    eq=s.Poly(s.expand(poly.subs(m,m+1)-2*poly+poly.subs(m,m-1)-source),m).coeffs()
    solution=s.solve(eq+[poly.subs(m,0),poly.subs(m,1)],cc)
    P[r]=s.factor(poly.subs(solution))
    assert s.expand(P[r].subs(m,m+1)-2*P[r]+P[r].subs(m,m-1)-source)==0
    assert P[r].subs(m,0)==P[r].subs(m,1)==P[r].subs(m,-1)==0

def poisson_half_expectation(poly):
    poly=s.Poly(s.cancel(poly),m)
    return s.simplify(sum(c*sum(s.functions.combinatorial.numbers.stirling(k[0],j,kind=2)*s.Rational(1,2)**j for j in range(k[0]+1)) for k,c in poly.terms()))

ratios={r:s.factor(poisson_half_expectation(P[r]/(m+1))) for r in P}
assert ratios[1]==0 and ratios[2]==B/72 and ratios[3]==s.Rational(1,288)
assert s.expand(ratios[4]+(13*B**2+80*L1)/5760)==0

# Audited diagonal coefficients L1=B²/18, L2=0, L3=−1/9.
vals={L1:B**2/18,L2:0,L3:-s.Rational(1,9)}
leaf_log=cut(-s.Rational(2,3)*s.log(1-t**3)+B/t*((1-t**3)**s.Rational(1,3)-1)+L1*phi+L2*phi**2+L3*phi**3+s.log(sum(ratios[r]*phi**r for r in range(4))))
leaf_first3=[s.factor(leaf_log.coeff(t,r).subs(vals)) for r in range(1,4)]
assert leaf_first3==[B**2/18,-23*B/72,s.Rational(161,288)]

# Compare triangular rows with the rigorous Chang et al. word recurrence.
A=[[1]]; W={}
for n in range(1,21):
    row=[(2*n-1)*A[-1][0]]
    for k in range(1,n+1):row.append(row[-1]+(2*n+k-1)*(A[-1][k] if k<n else 0))
    A.append(row)
    for k in range(n+1):
        for h in range(1,n+1):
            W[n,k,h]=(int(k in (0,1)) if n==1 else sum(W.get((n-1,k,j),0) for j in range(1,h+1))+(n+h+k-2)*sum(W.get((n-1,k-1,j),0) for j in range(1,h+1)))
        c=sum(W[n,k,h] for h in range(1,n+1))
        assert c==Fraction(A[n][k]*2**(n-k),factorial(n-k+1))
    for d in range(n+1):
        assert Fraction(A[n][n-d],A[n][n])<=Fraction(d+1,2**d)

report={
    'P':{r:str(P[r]) for r in P},
    'ratio_coefficients':{r:str(ratios[r]) for r in ratios},
    'ratio_coefficients_audited_diagonal':{r:str(s.factor(ratios[r].subs(vals))) for r in ratios},
    'leaf_log_first_three':list(map(str,leaf_first3)),
    'formal_recursion_checked_through_order':R,
    'exact_word_identity_and_deficit_bound_checked_through':20,
    'caution':'Finite checks support, but do not replace, the mathematical proof.'
}
(ROOT/'total-transfer-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
