"""Exact polynomial-pair arithmetic. No floating-point or file IO is used here."""
import sympy as S

x, k, t, a = S.symbols('x k t a')
ORDER = 9

class VerificationError(RuntimeError):
    """A required verification condition failed."""

def require(condition, label):
    if not condition:
        raise VerificationError(label)

def zero(expr):
    return S.expand(expr) == 0

def add(left, right):
    require(len(left) == len(right), 'pair/series shape mismatch')
    return [S.expand(u + v) for u, v in zip(left, right)]

def derivative(pair):
    p, q = pair
    return [S.expand(S.diff(p, x) + (2*x+k)*q), S.expand(p+S.diff(q,x))]

def airy_operator(pair):
    return add(derivative(derivative(pair)), [-S.expand((2*x+k)*v) for v in pair])

def multiply(left, right, order):
    out = [S.S.Zero] * (order+1)
    for i, u in enumerate(left[:order+1]):
        if u == 0:
            continue
        for j, v in enumerate(right[:order+1-i]):
            if v != 0:
                out[i+j] += u*v
    return [S.expand(v) for v in out]

def series(expr, order):
    return S.series(expr, t, 0, order+1).removeO().expand()

def coefficients(expr, order):
    result = series(expr, order)
    return [result.coeff(t,j) for j in range(order+1)]

def shift(pair, index, lag, direction, order):
    # t_lag^index f_index((x+direction*t)(1-lag*t^3)^(-1/3)).
    factor = [S.S.Zero]*(order+1)
    for j in range((order-index)//3+1):
        factor[index+3*j] = S.rf(S.Rational(index,3),j)*lag**j/S.factorial(j)
    stretch = [S.S.Zero]*(order+1)
    for j in range(order//3+1):
        stretch[3*j] = S.rf(S.Rational(1,3),j)*lag**j/S.factorial(j)
    delta = [S.expand(x*stretch[j]+(direction*stretch[j-1] if j else 0)-(x if j==0 else 0)) for j in range(order+1)]
    power = [S.S.One]+[S.S.Zero]*order
    out = [[S.S.Zero]*(order+1) for _ in range(2)]
    for d in range(order-index+1):
        scalar = multiply(factor,power,order)
        for component in range(2):
            for j in range(order+1):
                out[component][j] += scalar[j]*pair[component]/S.factorial(d)
        power = multiply(power,delta,order)
        pair = derivative(pair)
    return [[S.expand(v) for v in component] for component in out]

def fullshift(profiles,lag,direction,order):
    out = [[S.S.Zero]*(order+1) for _ in range(2)]
    for j,pair in enumerate(profiles):
        shifted = shift(pair,j,lag,direction,order)
        out = [add(u,v) for u,v in zip(out,shifted)]
    return out

def recurrence_rhs(profiles,sigma,kind,order):
    require(kind in ('R','C'), 'unsupported sequence')
    weight = coefficients((1-x*t*t+3*t**3)/(1+x*t*t-t**3),order)
    minus = fullshift(profiles,1,-1,order)
    plus = fullshift(profiles,1,1,order)
    rhs = [add(multiply(weight,u,order),v) for u,v in zip(minus,plus)]
    if kind == 'C':
        shifted_sigmas = [coefficients(sum(sigma[j]*t**j*(1-q*t**3)**(-S.Rational(j,3)) for j in range(len(sigma))),order) for q in (1,2)]
        product = multiply(*shifted_sigmas,order)
        require(product[0] != 0, 'zero compacted denominator')
        inverse = [S.S.Zero]*(order+1)
        inverse[0] = 1/product[0]
        for j in range(1,order+1):
            inverse[j] = -S.expand(sum(product[i]*inverse[j-i] for i in range(1,j+1)))/product[0]
        factor = multiply(coefficients(2*t**3*(1-x*t*t-t**3)/((1+x*t*t-t**3)*(1+x*t*t-3*t**3)),order),inverse,order)
        other = fullshift(profiles,3,-1,order)
        rhs = [add(u,[-v for v in multiply(factor,w,order)]) for u,w in zip(rhs,other)]
    return rhs

def solve_triangular(residual):
    target = S.Poly(S.expand(2*residual[0]-S.diff(residual[1],x)),x)
    degree = 0 if target.is_zero else int(target.degree())
    values = [S.S.Zero]*(degree+4)
    for d in range(degree,-1,-1):
        values[d] = S.expand((-target.nth(d)-4*k*(d+1)*values[d+1]+(d+3)*(d+2)*(d+1)*values[d+3])/(4*(2*d+1)))
    qtilde = sum(values[d]*x**d for d in range(degree+1))
    sigma = -2*values[0]
    q = S.expand(qtilde+sigma/2)
    p = S.integrate((-residual[1]-S.diff(q,x,2))/2,x)-S.diff(q,x).subs(x,0)
    return [S.expand(p),q], S.expand(sigma)

def solve_generic(residual,index):
    # Generic exact linear solve: no use of the triangular inverse above.
    degree = 2*index+2
    ps = S.symbols(f'p0:{degree+1}')
    qs = S.symbols(f'q0:{degree+1}')
    sigma = S.Symbol('sigma')
    p = sum(ps[j]*x**j for j in range(degree+1))
    q = sum(qs[j]*x**j for j in range(degree+1))
    equation = add(airy_operator([p,q]),add(residual,[-sigma,0]))
    constraints = S.Poly(equation[0],x).all_coeffs()+S.Poly(equation[1],x).all_coeffs()+[q.subs(x,0),(p+S.diff(q,x)).subs(x,0)]
    unknowns = (*ps,*qs,sigma)
    solution_set = S.linsolve(constraints,unknowns)
    require(solution_set != S.EmptySet and len(solution_set)==1, 'generic solver did not return one solution')
    solution = tuple(next(iter(solution_set)))
    require(len(solution)==len(unknowns), 'generic solver output shape')
    require(not any(v.free_symbols.intersection(unknowns) for v in solution), 'generic solver left undetermined coefficients')
    mapping = dict(zip(unknowns,solution))
    return [S.expand(p.subs(mapping)),S.expand(q.subs(mapping))],S.expand(mapping[sigma])

def construct(kind):
    profiles = [[S.S.One,S.S.Zero]]
    sigma = [S.S(2),S.S.Zero,k]
    stages = 0
    for order in range(3,ORDER+1):
        rhs = recurrence_rhs(profiles,sigma,kind,order)
        residual = [S.expand(rhs[c][order]-sum(sigma[order-j]*profiles[j][c] for j in range(len(profiles)) if 0<=order-j<len(sigma))) for c in range(2)]
        pair,new_sigma = solve_triangular(residual)
        generic,generic_sigma = solve_generic(residual,order-2)
        require(all(zero(u-v) for u,v in zip(pair,generic)) and zero(new_sigma-generic_sigma), f'{kind}: triangular/generic solver disagreement at {order}')
        require(all(zero(v) for v in add(airy_operator(pair),add(residual,[-new_sigma,0]))),f'{kind}: construction residual at {order}')
        require(zero(pair[1].subs(x,0)) and zero((pair[0]+S.diff(pair[1],x)).subs(x,0)),f'{kind}: construction gauge at {order}')
        profiles.append(pair)
        sigma.append(new_sigma)
        stages += 1
    require(stages==7 and len(profiles)==8 and len(sigma)==10, f'{kind}: incomplete construction')
    return profiles,sigma

def endpoint_series(profiles,order=6):
    result = S.S.Zero
    for j,initial in enumerate(profiles):
        pair = initial
        for p in range(order+2-j):
            result += pair[1].subs(x,0)*t**(j+p-1)/S.factorial(p)
            pair = derivative(pair)
    result = series(result,order)
    require(result.coeff(t,0)==1, 'endpoint normalization')
    return result

def integrate_endpoint(profiles,sigma):
    order = ORDER-3
    logs = series(S.log(sum(sigma[j]*t**j for j in range(ORDER+1))/2),ORDER)
    difference = S.Rational(3,2)*k/t*(1-(1-t**3)**S.Rational(1,3))-sigma[3]/2*S.log(1-t**3)
    ell = []
    for j in range(1,order+1):
        coefficient = S.factor((series(difference,j+3).coeff(t,j+3)-logs.coeff(t,j+3))*3/j)
        ell.append(coefficient)
        difference += coefficient*t**j*(1-(1-t**3)**(-S.Rational(j,3)))
    require(zero(series(difference,ORDER)-logs), 'formal discrete integration residual')
    E = endpoint_series(profiles,order)
    logE = series(S.log(E),order)
    log_coeffs = [S.simplify((ell[j-1]+logE.coeff(t,j)).subs(k,2**S.Rational(2,3)*a)*2**(-S.Rational(j,3))) for j in range(1,order+1)]
    correction = series(S.exp(sum(log_coeffs[j-1]*t**j for j in range(1,order+1))),order)
    multiplicative = [S.expand(correction.coeff(t,j)) for j in range(order+1)]
    return E,log_coeffs,multiplicative

def direct_ratio(E,sigma):
    st = sum(sigma[j]*t**j for j in range(ORDER+1))
    st1 = series(sum(sigma[j]*t**j*(1-t**3)**(-S.Rational(j,3)) for j in range(ORDER+1)),ORDER)
    t2 = t*(1-2*t**3)**(-S.Rational(1,3))
    shiftedE = series(E.subs(t,t2),ORDER)
    qr = series(st*st1/4*(1-2*t**3)**S.Rational(1,3)*E/shiftedE,ORDER)
    return [S.simplify(qr.coeff(t,j).subs(k,2**S.Rational(2,3)*a)*2**(-S.Rational(j,3))) for j in range(ORDER+1)]

def ratio_from_log(log_coeffs,kind):
    alpha = S.S.One if kind=='R' else S.Rational(3,4)
    logarithm = 3*a/t*(1-(1-t**3)**S.Rational(1,3))-alpha*S.log(1-t**3)
    for j,coefficient in enumerate(log_coeffs,1):
        logarithm += coefficient*t**j*(1-(1-t**3)**(-S.Rational(j,3)))
    ratio = series(S.exp(series(logarithm,ORDER)),ORDER)
    return [S.expand(ratio.coeff(t,j)) for j in range(ORDER+1)]
