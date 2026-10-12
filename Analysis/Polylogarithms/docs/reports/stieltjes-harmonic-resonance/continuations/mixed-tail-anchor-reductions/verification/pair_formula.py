"""Independent one-tail Faulhaber formula for every odd centered (2,3) moment."""
import sympy as s
from research import N,Z

def power_sum(r):
    return s.expand((s.bernoulli(r+1,N+1)-s.bernoulli(r+1,1))/s.Integer(r+1))

def pair_value(m):
    if not isinstance(m,int) or m<1 or m%2!=1:raise ValueError('m must be a positive odd integer')
    P=s.Poly((s.bernoulli(m+1,N+s.Rational(1,2))-s.bernoulli(m+1,s.Rational(1,2)))/s.Integer(m+1),N)
    p2=P.nth(2);Q=P.as_expr()-p2*N**2
    R=sum(c*power_sum(h[0]-3) for h,c in s.Poly(Q,N).terms() if c)
    S=sum(c*power_sum(h[0]-2) for h,c in s.Poly(Q,N).terms() if c)
    L=sum(c*s.bernoulli(h[0]-2) for h,c in P.terms())
    u=s.symbols('u');K=m+3
    a=u-u**2/2+sum(s.bernoulli(2*j)*u**(2*j+1) for j in range(1,K))
    b=u**2/2-u**3/2+sum(s.bernoulli(2*j)*s.rf(3,2*j-1)/s.factorial(2*j)*u**(2*j+2) for j in range(1,K))
    rho=s.expand(Q.subs(N,1/u)*a*b+s.sympify(R).subs(N,1/u)*a+s.sympify(S).subs(N,1/u)*b).coeff(u,0)
    return s.expand(p2*Z((3,))+L*Z((2,))+rho)

def telescoper_residual():
    n,A,B=s.symbols('n A B');x=n+s.Rational(1,2)
    T=8*n**4*(5*n*n+1)*A*B+2*n*(n+1)*(5*n*n+5*n+2)*A+4*n*n*(n+1)**2*(2*n+1)*B-34*n**3+9*n*n-33*n
    nxt=T.subs(n,n+1).subs({A:A-(n+1)**-2,B:B-(n+1)**-3},simultaneous=True)
    return s.factor(nxt-T-((23*x+232*x**3+240*x**5)*A*B-120*x*x-76))
