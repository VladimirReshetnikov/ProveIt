import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Exact formal inverse cancellations, with logarithms represented by polynomials.

The symbolic first two identities and synthetic higher-order checks verify
finite algebra. Eventual monotonicity, error bounds, and inside-ceiling
sandwiches are proved in the article, not by these finite examples.
"""
from fractions import Fraction as F
from exact_algebra import (add, scale, multiply, power, constant, variable,
    series_add, series_scale, series_log, series_inverse, series_power,
    series_multiply, require, rational_strings)


def compose_polynomial(poly, series, order, dimension=1):
    """Substitute a formal series into a univariate rational polynomial."""
    result=[{} for _ in range(order+1)]
    for (degree,),coefficient in poly.items():
        result=series_add(result,series_scale(series_power(series,degree,order,dimension),coefficient))
    return result


def inverse_residual(Q,H,d,order):
    z=variable(0,1)
    # Q[0] is a=4z-d, Q[j] the coefficient at y^-j in w-y.
    u=[constant(1,1)]+Q[:order+1]
    logu=series_log(u,order,1)
    logw=[add(z,logu[0])]+logu[1:]
    invu=series_inverse(u,order,1)
    residual=(Q+[{} for _ in range(order+1)])[:order+1]
    residual[0]=add(residual[0],scale(z,-4),constant(d,1))
    residual=series_add(residual,series_scale(logu,-4))
    for j in range(1,min(order,len(H)-1)+1):
        composed=compose_polynomial(H[j],logw,order-j,1)
        factor=series_power(invu,j,order-j,1)
        term=series_multiply(composed,factor,order-j)
        residual=series_add(residual,[{} for _ in range(j)]+term)
    return residual


def inverse_polynomials(H,d,order):
    Q=[add(scale(variable(0,1),4),constant(-d,1))]
    for j in range(1,order+1):
        residual=inverse_residual(Q,H,d,j)
        Q.append(scale(residual[j],-1))
    require(all(not p for p in inverse_residual(Q,H,d,order)), 'inverse cancellation residual')
    return Q


def polynomial_record(poly):
    degree=max((p[0] for p in poly),default=0)
    return [str(poly.get((k,),F())) for k in range(degree+1)]


def first_two_symbolic():
    # Independent expansion over Q[z,d,lambda,beta,delta].
    z,d,lam,beta,delta=[variable(i,5) for i in range(5)]
    a=add(scale(z,4),scale(d,-1))
    h1=multiply(lam,beta)
    h2=multiply(power(lam,2),add(delta,scale(power(beta,2),F(-1,2))))
    Q1=add(scale(a,4),scale(h1,-1))
    Q2=add(scale(Q1,4),scale(power(a,2),-2),multiply(h1,a),scale(h2,-1))
    u=[constant(1,5),a,Q1,Q2]
    logu=series_log(u,2,5)
    invu=series_inverse(u,2,5)
    residual=[add(a,scale(z,-4),d),Q1,Q2]
    residual=series_add(residual,series_scale(logu,-4))
    residual=series_add(residual,[{},h1,multiply(h1,invu[1])])
    residual=series_add(residual,[{}, {}, h2])
    require(all(not p for p in residual),'symbolic Q1,Q2 cancellation')
    return 'Exact polynomial identity over Q[z,d,lambda,beta,delta]'


def checks():
    symbolic=first_two_symbolic()
    order=9
    z=variable(0,1)
    direct=[constant(1,1)]
    for j in range(1,order+1):
        base=constant(F((-1)**j*(2*j+1),j+2),1)
        direct.append(add(base,scale(z,F(j+1,j+3))) if j>=3 else base)
    L=series_log(direct,order,1)
    degrees=[]
    for j in range(1,order+1):
        degree=max((p[0] for p in L[j]),default=0)
        require(degree<=j//3,'log-direct polynomial degree bound')
        degrees.append(degree)
    # H_j(log w)=lambda^j L_j(log w-eta), eta represents log lambda.
    # Parameters are exact algebraic test values; no irrational numerical log is used.
    samples=[]
    for lam,eta,d in [(F(1),F(0),F(5,7)),(F(2),F(3,5),F(-4,3))]:
        H=[{}]
        shifted=[add(z,constant(-eta,1))]
        for j in range(1,order+1):
            H.append(scale(compose_polynomial(L[j],shifted,0)[0],lam**j))
        Q=inverse_polynomials(H,d,order)
        for j in range(1,order+1):
            require(max((p[0] for p in Q[j]),default=0)<=j,'inverse polynomial degree bound')
        samples.append({'lambda_formal_value':str(lam),'eta_formal_value':str(eta),
                        'd_formal_value':str(d),'Q1_through_Q9_ascending_coefficients':
                        [polynomial_record(p) for p in Q[1:]],
                        'zero_residual_orders':list(range(order+1))})
    return {'symbolic_Q1_Q2':symbolic,'direct_log_degrees_orders_1_to_9':degrees,
            'synthetic_samples':samples,
            'scope':'Formal exact cancellations. The second sample treats eta as an independent formal constant, not a numerical approximation to log(2). No integer-threshold value, effective onset, or exact rounding assertion is inferred.'}
