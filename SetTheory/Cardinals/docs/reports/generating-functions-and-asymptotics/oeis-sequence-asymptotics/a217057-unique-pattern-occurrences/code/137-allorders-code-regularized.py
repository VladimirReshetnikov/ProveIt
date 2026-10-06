import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Rigorously bounded regularized moments for one explicit SCALAR SYNTHETIC model.

This is not a numerical computation of the A217057 constants, in particular r_3.
The scalar residual 1/((n+1)...(n+s)) has beta-integral moments available exactly.
"""
from fractions import Fraction as F
from math import comb, factorial
from models import b, log_square
from exact_algebra import require, rational_strings

K = 6
S = 8
V = {3:F(2,7),4:F(-3,5),5:F(5,11),6:F(-7,13)}


def falling(n,j):
    result=1
    for k in range(j): result*=n-k
    return result


def residual(n):
    denominator=1
    for h in range(1,S+1): denominator*=n+h
    return F(1,denominator)


def a(n):
    return sum((v*b(k,n) for k,v in V.items()),F())+residual(n)


def residual_moment(j):
    require(0<=j<S-1,'moment convergence range')
    return F(factorial(j)**2*factorial(S-j-2),factorial(S-1)**2)


def T(j):
    return F((-1)**j,factorial(j))*residual_moment(j)


def partial_T(j,N):
    return F((-1)**j,factorial(j))*sum((falling(n,j)*(a(n)-sum(
        (V[k]*b(k,n) for k in range(3,min(j,K)+1)),F())) for n in range(N+1)),F())


def absolute_tail_bound(j,N):
    require(N>=2*K,'tail bound requires N >= 2K')
    # For n>N, |b_k(n)| <= k! 2^(k+1) n^(-k-1).
    # Sum n^(-p) from N+1 to infinity <= N^(1-p)/(p-1).
    value=F(1,(S-j-1)*N**(S-j-1))
    for k,v in V.items():
        if k>j:
            value += abs(v)*F(factorial(k)*2**(k+1),(k-j)*N**(k-j))
    return value/factorial(j)


def P_coefficient(n):
    return sum((T(j)*(-1)**n*comb(j,n) for j in range(n,K)),F()) if n<K else F()


def finite_convolution_model(n):
    single=F()
    for j in range(K):
        for k,v in V.items(): single+=2*T(j)*v*b(j+k,n)
    double=sum((v*w*log_square(k+ell,n) for k,v in V.items() for ell,w in V.items()),F())
    return single+double


def checks():
    rows=[]
    for j in range(4):
        previous_bound=None
        for N in (16,32,64,128):
            partial=partial_T(j,N)
            error=abs(partial-T(j))
            bound=absolute_tail_bound(j,N)
            require(error<=bound,'synthetic certified absolute tail bound')
            if previous_bound is not None:
                require(bound<previous_bound,'synthetic bound improves under doubled cutoff')
            previous_bound=bound
            rows.append({'j':j,'N':N,'absolute_error':str(error),'certified_upper_bound':str(bound)})
    # Exact zero moments of q=residual-P through K-1.
    for j in range(K):
        finite=sum((falling(n,j)*P_coefficient(n) for n in range(K)),F())
        require(finite==residual_moment(j),'synthetic vanishing falling-factorial moments')
    # Exact finite convolution diagnostics; scaling is informative, not a tail bound.
    convolution=[]
    for n in (32,64,128):
        exact=sum((a(t)*a(n-t) for t in range(n+1)),F())
        error=exact-finite_convolution_model(n)
        convolution.append({'n':n,'n_power_K_plus_2_times_error':str(n**(K+2)*error)})
    # The finite extension is consequential: changing b_3(0) changes T_0.
    require(b(3,0)==0 and b(3,1)==-1 and b(3,2)==F(5,2) and b(3,3)==F(-11,6),
            'exact finite model convention')
    return {'K':K,'residual_rising_factor_count':S,'singular_coefficients':{str(k):str(v) for k,v in V.items()},
            'exact_regularized_T0_through_T5':rational_strings(T(j) for j in range(K)),
            'tail_checks':rows,'vanishing_moment_orders':list(range(K)),
            'convolution_diagnostics':convolution,
            'scope':'Scalar synthetic model only. Bounds certify its regularized moments, not A217057 constants. Scaled convolution residuals are finite diagnostics, not certified uniform error bounds. No numerical r_3 or onset is claimed.'}
