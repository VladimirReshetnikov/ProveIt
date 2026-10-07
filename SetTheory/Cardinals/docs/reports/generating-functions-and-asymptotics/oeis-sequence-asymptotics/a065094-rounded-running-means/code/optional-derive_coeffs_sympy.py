#!/usr/bin/env python3
"""Optional original SymPy generator; standard-library formal_series.py is mandatory."""
import sympy as s
h=s.symbols('h'); J=9
c=s.symbols('c0:'+str(J+1)); known={c[0]:s.Integer(1)}
# h=n^-1/2, prefactor e^(2sqrt n)*n^-1/4
C=sum(c[j]*h**j for j in range(J+1))
def shift(sign):
    v=1+sign*h*h
    exponential=s.exp((2/h)*(s.sqrt(v)-1)).series(h,0,J+5).removeO()
    power=v**s.Rational(-1,4)
    cg=sum(c[j]*h**j*v**s.Rational(-j,2) for j in range(J+1))
    return s.series(exponential*power*cg,h,0,J+5).removeO()
r=s.series(shift(1)-2*C+(1-h*h)*shift(-1),h,0,J+5).removeO().expand()
for k in range(J+5):
    eq=s.expand(r.coeff(h,k).subs(known))
    free=eq.free_symbols
    if free:
        var=sorted(free,key=str)[0]; sol=s.solve(eq,var)
        if len(sol)==1: known[var]=sol[0]
print(known)
print('residue',s.expand(r.subs(known)))
