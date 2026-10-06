import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Exact singular-model identities, triangular matching, and kernel contractions."""
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
from exact_algebra import (add, multiply, scale, constant, variable, power,
    ordinary_series_inverse, ordinary_series_product, rational_strings, require)

@lru_cache(None)
def b(k, n):
    """Actual [z^n](1-z)^k log(1-z), including every small coefficient."""
    require(type(k) is int and type(n) is int and k >= 0 and n >= 0, 'model indices')
    return sum((F((-1)**(j+1)*comb(k,j), n-j)
                for j in range(min(k,n-1)+1)), F()) if n else F()


def harmonic(n):
    return sum((F(1,j) for j in range(1,n+1)), F())


def log_square(m,n):
    require(n > m, 'log-square closed form requires n>m')
    return 2*b(m,n)*(harmonic(m)-harmonic(n-m-1))

@lru_cache(None)
def homogeneous(k, degree):
    """h_degree(1,...,k), via complete-homogeneous recurrence."""
    h = [1]+[0]*degree
    for x in range(1,k+1):
        for j in range(1,degree+1):
            h[j] += x*h[j-1]
    return h[degree]


def b_asymptotic(k, inverse_power):
    if inverse_power < k+1:
        return F()
    return F((-1)**(k+1)*factorial(k)*homogeneous(k,inverse_power-k-1))


def singular_vectors(A):
    """Triangular V_3...V_{len(A)+2}; A is the input list of scalar tail coefficients U_j."""
    V = {}
    for k in range(3,len(A)+3):
        numerator = A[k-3] - sum((b_asymptotic(ell,k+1)*V[ell] for ell in V), F())
        V[k] = numerator / F((-1)**(k+1)*factorial(k))
    return V

@lru_cache(None)
def stirling2(n,k):
    if n == k == 0:
        return 1
    if n <= 0 or k <= 0 or k > n:
        return 0
    return k*stirling2(n-1,k)+stirling2(n-1,k-1)


def falling_coefficients(poly):
    degree = max((p[0] for p in poly), default=0)
    return [sum((c*stirling2(p[0],j) for p,c in poly.items()),F()) for j in range(degree+1)]


def kernel_1d(f,g):
    ff, gg = falling_coefficients(f), falling_coefficients(g)
    return 3*sum((a*c*factorial(p+q) for p,a in enumerate(ff) for q,c in enumerate(gg)),F())


def kernel_pair(X,Y):
    return sum((a*b*kernel_1d(f,h)*kernel_1d(g,k)
                for a,f,g in X for b,h,k in Y),F())


def kernel_values():
    x = variable(0,1)
    def shifted(k): return add(x,constant(k,1))
    d = scale(multiply(shifted(1),shifted(2)),F(1,2))
    e = scale(multiply(shifted(2),shifted(3)),F(1,6))
    da = scale(multiply(multiply(d,x),shifted(-1)),F(1,2))
    ea = scale(multiply(multiply(e,x),shifted(1)),F(1,2))
    C = [(F(81),e,e),(F(-9),d,d)]
    B = [(F(-648),e,e),(F(-81),ea,e),(F(-81),e,ea),
         (F(36),d,d),(F(9),da,d),(F(9),d,da)]
    return kernel_pair(C,C),kernel_pair(C,B)


def checks():
    # Independent finite definition vs rational falling-factorial formula.
    singles = 0
    for k in range(13):
        for n in range(k+1,65):
            expected = F((-1)**(k+1)*factorial(k)*factorial(n-k-1),factorial(n))
            require(b(k,n)==expected,'singular-model exact coefficient')
            singles += 1
    squares = 0
    for m in range(13):
        for k in range(m+1):
            ell = m-k
            for n in range(m+1,65):
                actual = sum((b(k,t)*b(ell,n-t) for t in range(n+1)),F())
                require(actual==log_square(m,n),'every split of the log-square model')
                squares += 1
    small = {str(k):rational_strings(b(k,n) for n in range(k+1)) for k in range(3,7)}
    # Match the recurrence on each basis vector, not just a single numerical tail.
    vector_columns = []
    for j in range(8):
        A = [F(int(i==j)) for i in range(8)]
        V = singular_vectors(A)
        for order in range(4,12):
            require(sum((b_asymptotic(k,order)*v for k,v in V.items()),F())==A[order-4],
                    'triangular model-to-tail reconstruction')
        vector_columns.append(V)
    first = [[vector_columns[j][k] for j in range(4)] for k in range(3,7)]
    expected_first = [[F(1,6),0,0,0],[F(1,4),F(-1,24),0,0],
                      [F(7,24),F(-1,12),F(1,120),0],
                      [F(5,16),F(-17,144),F(1,48),F(-1,720)]]
    require(first==expected_first,'V_3 through V_6 coefficients')
    first_c = [[b_asymptotic(k,p) for k in range(3,7)] for p in range(4,8)]
    require(first_c==[[6,0,0,0],[36,-24,0,0],[150,-240,120,0],[540,-1560,1800,-720]],
            'c_0 through c_3 single-log weights')
    # -2 b_6(n) supplies 1440 n^-7 + 30240 n^-8 log n;
    # two V_3 V_4 copies of -2 b_7 supply -20160 n^-8.
    require(-2*b_asymptotic(6,7)==1440 and -2*b_asymptotic(6,8)==30240 and
            -4*b_asymptotic(7,8)==-20160,'logarithmic convolution weights')
    require(F(1440,36)==40 and F(30240,36)-F(20160*6,144)==0 and F(20160,144)==140,
            'ell_3 and ell_4 cancellations')
    alpha = [F(1),F(-11,2),F(20),F(-965,16)]
    inverse = ordinary_series_inverse(alpha,3)
    require(inverse==[1,F(11,2),F(41,4),F(107,16)],'inverse avoidance through order three')
    weights = []
    for j in range(4):
        shifted = [F(comb(3+j+h,h)*4**h) for h in range(4-j)]
        weights.append(ordinary_series_product(shifted,inverse,3-j)[3-j])
    require(weights==[F(37291,16),F(1441,4),F(59,2),1],'r_3 fixed-shift weights')
    require(7*4+inverse[1]==F(67,2),'fourth logarithm shift and division')
    cc,cb = kernel_values()
    require((cc,cb)==(1393848,-52348032),'C,C and C,B exact kernel contractions')
    k3 = F(81,16*9**4)*40*cc
    k4 = F(81,16*9**4)*(570*cc+140*cb)
    require(k3==43020 and k4==-5041845,'exact logarithmic constants')
    return {'single_log_checks':singles,'log_square_checks':squares,
            'small_model_coefficients':small,'V3_through_V6_rows':list(map(rational_strings,first)),
            'single_log_c_rows':list(map(rational_strings,first_c)),
            'avoidance_inverse':rational_strings(inverse),'r3_shiftweights_c0_to_c3':rational_strings(weights),
            'kappa4_shiftweight':'67/2','kernel_CC':str(cc),'kernel_CB':str(cb),
            'kappa3_in_sqrt3_over_pi_units':str(k3),'kappa4_in_sqrt3_over_pi_units':str(k4),
            'scope':'Exact finite identities only. The article proves convergence, uniform analytic estimates, and all-order error control.'}
