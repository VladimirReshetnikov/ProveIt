"""Exact all-parameter certificate for the p=6 optimal-prefix reduction.

The algebraic determinant identities are polynomial identities in b,
not identities fitted at finitely many integer values. The direct
Bernoulli determinants at sample sizes are separate cross-checks.
"""
import json
import sympy as s
from pathlib import Path
from functools import reduce
b,z=s.symbols('b z',integer=True)
a=3
B={o:s.Symbol('B'+str(-o)) for o in range(-(2*a-1),0)}

def falling(x,n): return s.prod(x-j for j in range(n))
def f(l,n): return s.prod((2*n-r)*(2*n+3+r) for r in range(2*l))/s.factorial(2*l+1)
def facratio(X,Y,diff):
 return s.prod(Y+j for j in range(1,diff+1)) if diff>=0 else 1/s.prod(X+j for j in range(1,-diff+1))
F=s.zeros(a); A=s.zeros(a)
for i in range(a):
 n=b-a+i
 for l in range(a):
  N=2*(n-l)+1
  P=(z+2*l+1)*falling(2*n+2*l+z+1,2*i)
  total=0
  for h in range(1,2*i+2,2):
   coeff=s.expand(sum((-1)**(h-j)*s.binomial(h,j)*P.subs(z,N-j) for j in range(h+1))/s.factorial(h))
   offset=-a+i-l+(1-h)//2
   total += coeff*falling(N,h)*B[offset]
  R=2*b-2*a+2+2*l
  diff=1+4*l-2*i
  C=2*facratio(R,N,diff)/((2*n+1)*(2*n+2)*s.factorial(2*l+2))
  F[i,l]=s.factor(f(l,n))
  A[i,l]=s.factor(2*F[i,l]+C*total)
Fdet = 16*(b-1)*(2*b-3)*(4*b-7)*(4*b-5)*(4*b-3)*(16*b**4-80*b**3+80*b**2+50*b+9)/45
assert s.cancel(F.det()-Fdet) == 0
Ad=s.factor(A.det(method='domain-ge'))
ratio=s.factor(Ad/F.det())
num,den=s.fraction(ratio)
# Present coefficient valuations after replacing B by odd half-integers.
V={o:s.Symbol('U'+str(-o)) for o in B}
expr=s.factor(8*ratio.subs({B[o]:V[o]/2 for o in B}))
num8,den8=s.fraction(expr)
D = 16*b**4-80*b**3+80*b**2+50*b+9
Q = 512*b**6-6656*b**5+27296*b**4-25200*b**3-91092*b**2+217836*b-123741
P = s.cancel(48*(2*b-3)*D*ratio.subs({B[o]:V[o]/2 for o in B}))
P = s.Poly(P,b,*V.values(),domain=s.ZZ).as_expr()
assert s.expand(P.subs({v:1 for v in V.values()})+2*(2*b-5)*Q) == 0
assert s.Poly(D,b,modulus=2).as_expr() == 1
assert s.Poly(Q,b,modulus=2).as_expr() == 1

def direct(a_value,b_value):
    mu=lambda n:s.bernoulli(2*n)/s.factorial(2*n) if n>=0 else s.S.Zero
    H=s.Matrix(b_value,b_value,lambda t,k:mu(t+k-a_value+1))
    J=s.Matrix(b_value,b_value,lambda t,k:mu(t+k-a_value+1)*(1+(
        s.factorial(2*t+1)*s.factorial(2*b_value-2*k)/(
        s.factorial(2*a_value-2*k)*s.factorial(2*b_value+2*t-2*a_value+1))
        if k<a_value else 0)))
    ratio_value=s.cancel(J.det(method='domain-ge')/H.det(method='domain-ge'))
    factor=s.prod(s.factorial(2*b_value+2*t-2*a_value+1) for t in range(b_value))
    factor/=s.prod(s.factorial(2*b_value-2*k) for k in range(b_value))
    return ratio_value,s.cancel(J.det(method='domain-ge')*factor)

small_expected={4:s.Rational(7527,1240),5:s.Rational(713039,70280),6:s.Rational(2968099,1116360)}
direct_checks={}
for bv in range(4,13):
    rv,md=direct(3,bv)
    if bv in small_expected: assert rv == small_expected[bv]
    if bv>=6:
        symbolic=ratio.subs({b:bv,**{B[o]:s.bernoulli(2*bv+2*o) for o in B}})
        assert s.cancel(symbolic-rv)==0
    direct_checks[str(bv)]={"ratio":str(rv),"M_determinant":str(md)}
obstruction,_=direct(4,9)
assert obstruction==s.Rational(-334092867653747,85606130610)
payload={"status":"exact symbolic assertions passed", "F_determinant":str(Fdet),
         "D":str(D),"Q":str(Q),"P":str(P),
         "P_at_all_U_equal_one":str(-2*(2*b-5)*Q),
         "normalized_matrix":str(A),"direct_checks":direct_checks,
         "uniform_valuation_counterexample":{"a":4,"b":9,"ratio":str(obstruction),"v2":-1}}
output=Path(__file__).resolve().parent.parent.joinpath("results", "verify_moment_rank_six.json")
output.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({"status":payload["status"],"output":str(output),
                  "symbolic_identity":"8 ratio = P / [6(2b-3)D]", 
                  "P_at_U_one":str(s.factor(P.subs({v:1 for v in V.values()}))),
                  "direct_checks":list(direct_checks),"counterexample":str(obstruction)},indent=2))
