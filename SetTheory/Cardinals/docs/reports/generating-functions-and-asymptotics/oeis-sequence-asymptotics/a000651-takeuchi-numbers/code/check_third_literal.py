#!/usr/bin/env python3
"""Independent literal-formula audit; never imports or mutates the report package."""
import sympy as s
w,k,i=s.symbols('w k i')
d=w/(1+w)
g=w*w/2-s.log(1+w)/2
p1=-w*w*(26*w*w+67*w+46)/(24*(1+w)**3)
p2=-w*w*(12*w**6+100*w**5+310*w**4+457*w**3+310*w*w+36*w-54)/(48*(1+w)**6)
P=240*w**11-432*w**10-30420*w**9-225880*w**8-844658*w**7-1925812*w**6-2813239*w**5-2533360*w**4-1073820*w**3+334112*w**2+728528*w+367728
Q=240*w**10-592*w**9-29028*w**8-188952*w**7-607146*w**6-1152408*w**5-1338579*w**4-884496*w**3-205104*w**2+133296*w+103040
H3=-w**4*P/(5760*(1+w)**10)
p3=w**3*Q/(17280*(1+w)**9)
can=s.cancel
Dq=lambda f,q:can(d*s.diff(f,w)-q*f)
j=k+1
A={r:can((-k**r+(-1)**(r+1)*s.summation(i**r,(i,0,k-1)))/r) for r in range(1,5)}
# F first derivative w is canceled exactly against the leading factor.
f=w
for t in range(2,6):
    f=Dq(f,t-2)
    A[t-1]+=(-j)**t*f/s.factorial(t)
# Remaining smooth terms: each differentiation increments the h exponent.
for q,f0 in [(0,g),(1,p1),(2,p2)]:
    f=f0
    for t in range(1,5-q):
        f=Dq(f,q+t-1)
        A[q+t]+=(-j)**t*f/s.factorial(t)
R=s.QQ.frac_field(w)
Ap={r:s.Poly(f,k,domain=R) for r,f in A.items()}
B={0:s.Poly(1,k,domain=R)}
for r in range(1,5):
    B[r]=sum((Ap[t]*B[r-t]).mul_ground(s.Rational(t,r)) for t in range(1,r+1))
# Independent Poisson moments, using M_{m+1}=w(M_m'+M_m).
M=[s.Integer(1)]
for m in range(8): M.append(s.expand(w*(s.diff(M[-1],w)+M[-1])))
def expectation(poly): return can(sum(coef*M[power[0]] for power,coef in poly.terms()))
expect=[expectation(B[r]) for r in range(1,5)]
assert expect[:3]==[0,0,0]
assert can(expect[3]-H3)==0
print('Independent raw product / differential jet / Poisson-moment derivation: H3 exactly matches; lower three residuals vanish.')
ode=can(-w*s.diff(p3,w)+3*(w+1)*p3+H3)
assert ode==0
print('Canonical ODE residual =',ode)
lead=s.limit(p3/w**4,w,s.oo)
assert lead==s.Rational(1,72)
print('p3/w^4 limit =',lead)
# Bound rational coefficient at infinity by numerator-degree minus denominator-degree.
def degree(f):
    num,den=can(f).as_numer_denom()
    return int(s.degree(num,w)-s.degree(den,w)) if num!=0 else -999
# Pole denominators consist only of positive factors 1+w and fixed constants.
def no_nonpositive_axis_poles(f):
    _,den=can(f).as_numer_denom()
    for base,power in s.factor_list(den,w)[1]:
        assert base in (w+1,w), (base,power)
# Check coefficients of final A4 (after p3) under weighted X-degree.
Ap[4]-=s.Poly(j*Dq(p3,3),k,domain=R)
for r in range(1,5):
    degrees=[]
    for power,coef in Ap[r].terms():
        no_nonpositive_axis_poles(coef)
        degrees.append(power[0]+max(0,degree(coef)))
    assert max(degrees)<=r+1
    print('A%d maximum joint growth degree ='%r,max(degrees),'<=',r+1)
# Derivative remainder coefficients. F^(6)=n^-5 phi6 etc.
for label,q,f0,t,bound in [('Fprime',0,w,5,0),('g',0,g,5,1),('p1/n',1,p1,4,1),('p2/n2',2,p2,3,2),('p3/n3',3,p3,2,4)]:
    f=f0
    for a in range(t): f=Dq(f,q+a)
    actual=degree(f)
    assert actual<=bound,(label,actual,bound)
    no_nonpositive_axis_poles(f)
    print(label,'remainder coefficient growth degree =',actual,'<=',bound)
print('ALL INDEPENDENT EXACT CHECKS PASS')
