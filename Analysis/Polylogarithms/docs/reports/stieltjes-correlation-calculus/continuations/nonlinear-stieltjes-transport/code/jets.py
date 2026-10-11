"""Finite ordinary power series. Coefficients may be Fraction or mpmath numbers.
Every operation truncates at the input precision; no analytic convergence is implied.
"""
from math import factorial
from fractions import Fraction as Q

def divide(a,b):
    if isinstance(a,(int,Q)) and isinstance(b,(int,Q)): return Q(a)/Q(b)
    return a/b

def constant(c, n): return [c] + [0]*n

def add(a,b): return [x+y for x,y in zip(a,b)]

def scale(a,c): return [c*x for x in a]

def mul(a,b):
    n=min(len(a),len(b))-1
    return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(n+1)]

def inv(a):
    if a[0] == 0: raise ZeroDivisionError('A series inverse needs a nonzero constant.')
    n=len(a)-1; b=[divide(1,a[0])]+[0]*n
    for k in range(1,n+1): b[k]=divide(-sum(a[j]*b[k-j] for j in range(1,k+1)),a[0])
    return b

def power(a,k):
    if k<0: return power(inv(a),-k)
    ans=constant(1,len(a)-1); base=a
    while k:
        if k&1: ans=mul(ans,base)
        k//=2
        if k: base=mul(base,base)
    return ans

def derivative(a): return [(j+1)*a[j+1] for j in range(len(a)-1)] + [0]

def integral(a,zero=0): return [zero]+[divide(a[j],j+1) for j in range(len(a)-1)]

def logarithm(a, log_constant=0):
    """Specify log(a[0]); exact code usually passes a formal symbol or zero."""
    return integral(mul(derivative(a),inv(a)),log_constant)

def compose(a,b):
    if b[0]!=0: raise ValueError('Truncated composition requires b[0] == 0.')
    out=constant(0,len(b)-1)
    for c in reversed(a): out=add(mul(out,b),constant(c,len(b)-1))
    return out

def reverse(phi):
    if phi[0]!=0 or phi[1]==0: raise ValueError('Reversion needs phi(0)=0, phi\'(0)!=0.')
    n=len(phi)-1; out=[0]*(n+1)
    for k in range(1,n+1):
        out[k]=divide((1 if k==1 else 0)-compose(phi,out)[k],phi[1])
    return out

def eval_series(a,x):
    out=0
    for c in reversed(a): out=out*x+c
    return out

def elementary(p):
    """e[p,j] = elementary symmetric polynomial of 1,1/2,...,1/p."""
    from fractions import Fraction as Q
    e=[Q(1)]+[Q(0)]*p
    for k in range(1,p+1):
        for j in range(k,0,-1): e[j]+=e[j-1]/k
    return e

def t_polynomial(m,p,L):
    e=elementary(p)
    out=constant(0,len(L)-1)
    for j in range(min(m,p)+1):
        out=add(out,scale(power(L,m-j+1),(-1)**j*factorial(m)*e[j]/factorial(m-j+1)))
    return out

def contact_monomial(phi,k,n,h,log_slope=0):
    """Action of phi*FP(x^-k log^n x dx)-FP(phi'phi^-k log^n phi dy).
    phi must be known to degree >= k. h is an ordinary test-function jet.
    """
    r=phi[1:]+[0]; L=logarithm(r,log_slope)
    a=mul(derivative(phi),power(r,-k))
    return divide(mul(mul(a,power(L,n+1)),h)[k-1],n+1)

def contact_stieltjes(phi,m,p,h,log_slope=0):
    r=phi[1:]+[0]; L=logarithm(r,log_slope)
    a=mul(derivative(phi),power(r,-p-1))
    return (-1)**p*factorial(p)*mul(mul(a,t_polynomial(m,p,L)),h)[p]
