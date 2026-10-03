import sympy as s
w,k,h,r=s.symbols('w k h r')
d=w/(1+w)
g=w*w/2-s.log(1+w)/2
p=-w*w*(26*w*w+67*w+46)/(24*(1+w)**3)
q=-w*w*(12*w**6+100*w**5+310*w**4+457*w**3+310*w*w+36*w-54)/(48*(1+w)**6)
D=lambda x:s.expand(h*d*s.diff(x,w)-h*h*s.diff(x,h))
# Differentiate the full explicit log model after substituting F'=w,
# rather than the residual-script's recurrence of derivative coefficients.
Lprime=w+D(g+h*p+h*h*q)
series=s.S(0); deriv=Lprime
for degree in range(1,5):
    series += (-(k+1))**degree/s.factorial(degree)*deriv
    deriv=D(deriv)
# Exact log of (1-k/n) product_{r=0}^{k-1}(1+r/n), through h^3.
for degree in range(1,4):
    series += h**degree/degree*(-k**degree+(-1)**(degree+1)*s.summation(r**degree,(r,0,k-1)))
series=s.expand(series+(k+1)*w)
A=[s.cancel(series.coeff(h,i)) for i in (1,2,3)]
E=lambda a:s.factor(sum(coeff*s.bell(powers[0],w) for powers,coeff in s.Poly(s.cancel(a),k).terms()))
res=[E(A[0]),E(A[1]+A[0]**2/2),E(A[2]+A[0]*A[1]+A[0]**3/6)]
print('Independently differentiated Poisson residual coefficients:',res)
assert res==[0,0,0]
ct1=s.cancel(p/w);ct2=s.cancel(q/w**2)
cb1=-w*(2*w*w+7*w+10)/(24*(1+w)**3)
cb2=-w*(2*w**4+12*w**3+29*w*w+40*w+36)/(48*(1+w)**6)
tb1=-w*(2*w+3)/(2*(1+w)**2)
tb2=-(6*w**5+43*w**4+106*w**3+108*w*w+27*w-27)/(24*(1+w)**5)
print('Takeuchi minus Bell first coefficient residual:',s.factor(ct1-cb1-tb1))
print('Takeuchi minus Bell second coefficient residual:',s.factor(ct2-cb2-tb2))
assert s.factor(ct1-cb1-tb1)==0
assert s.factor(ct2-cb2-tb2)==0
print('Direct exponential correction limits:',s.limit(ct1,w,s.oo),s.limit(ct2,w,s.oo))
print('Ratio exponential correction limits:',s.limit(tb1,w,s.oo),s.limit(tb2,w,s.oo))
print('All checks passed; these are algebraic corroboration, not the analytic proof.')
