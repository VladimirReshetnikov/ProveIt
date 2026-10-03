"""Exact formal residue-weight expansion. No numerical fitted coefficients."""
import sympy as s
z,j,l=s.symbols('z j l')
M=7

def poisson_mean(poly,theta=1):
    p=s.Poly(s.expand(poly),j)
    return s.expand(sum(c*s.bell(m[0],theta) for m,c in p.terms()))

def prod_series(offset):
    # product over l=offset,...,j+offset-1 of (1-l*z)^(-1)
    L=sum(z**m*s.summation(l**m,(l,offset,j+offset-1))/m for m in range(1,M+1))
    out=[s.Integer(1)]
    # exponential coefficients c_n=(1/n) sum_i i*L_i*c_(n-i)
    for n in range(1,M+1):out.append(s.expand(sum(i*L.coeff(z,i)*out[n-i] for i in range(1,n+1))/n))
    return sum(poisson_mean(out[n])*z**n for n in range(M+1))
T0=prod_series(0);T1=prod_series(1)
B=s.series(T0-z*T1,z,0,M+1).removeO()
Q=s.series(B**-2,z,0,M+1).removeO()
# ratio w_k / [(e^-2/sqrt(2pi))*k^-3/2*e^k/k!]
# inverse Gamma(k) Stirling correction exp(-1/(12k)+1/(360k^3)-...)
G=s.series(s.exp(-sum(s.bernoulli(2*m)*z**(2*m-1)/(2*m*(2*m-1)) for m in range(1,(M+2)//2+1))),z,0,M+1).removeO()
D=s.series(Q*G,z,0,M+1).removeO()
for name,pol in [('normalized b',B),('inverse square',Q),('Dobinski weight correction',D)]:
 print(name,[pol.coeff(z,m) for m in range(M+1)])
