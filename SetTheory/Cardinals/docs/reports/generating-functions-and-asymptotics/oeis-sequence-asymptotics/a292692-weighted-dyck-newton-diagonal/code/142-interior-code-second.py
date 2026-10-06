#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Exact second-correction regeneration by Gaussian moments and endpoint sums.

No sequence data or fitted coefficients are used. Expected formulas are
compared only after independent derivation from the defining generating
functions and the polynomial recurrence.
"""
import sympy as S
from functools import lru_cache


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def rational_function(expression, variable):
    numerator, denominator = S.fraction(S.cancel(expression))
    numerator, denominator = S.Poly(numerator, variable), S.Poly(denominator, variable)
    leading = denominator.LC()
    return {'numerator': [str(S.cancel(numerator.nth(i)/leading)) for i in range(numerator.degree()+1)],
            'denominator': [str(S.cancel(denominator.nth(i)/leading)) for i in range(denominator.degree()+1)]}


def quadratic(expression):
    expanded = S.expand(S.radsimp(expression))
    a, b = expanded.collect(S.sqrt(17)).as_coeff_Add()
    b = S.simplify((expanded-a)/S.sqrt(17))
    require(a.is_Rational and b.is_Rational, 'quadratic field representation')
    return [str(a), str(b)]


def run():
    s=S.symbols('s',positive=True)
    l,r,u,x,y,eps=S.symbols('l r u x y eps')
    q=S.symbols('q',integer=True,nonnegative=True)
    t=1-s**2
    D=lambda a:S.cancel(-t*S.diff(a,s)/(2*s))
    f=1/s; h=f-1
    mu=S.cancel(D(h)/h); alpha=S.cancel(1/mu)
    Da=lambda a:S.cancel(S.diff(a,s)/S.diff(alpha,s))
    kappa={1:mu}; amp={1:S.cancel(D(f)/f)}
    for j in range(2,7): kappa[j]=D(kappa[j-1])
    for j in range(2,5): amp[j]=D(amp[j-1])
    B=kappa[2]

    # At theta=u/sqrt(m), the Gaussian-removed exponent is sum F_j z^j.
    # Its exponent combines the tilted h law, f amplitude, and the exact shifts.
    F={}
    for j in range(1,5):
        shift_amp=amp[j]-r*kappa[j]+(l if j==1 else 0)
        F[j]=S.expand(shift_amp*(S.I*u)**j/S.factorial(j)+kappa[j+2]*(S.I*u)**(j+2)/S.factorial(j+2))
    # If exp(sum F_j z^j)=sum E_j z^j then n E_n=sum j F_j E_(n-j).
    E=[S.Integer(1)]
    for n in range(1,5): E.append(S.expand(sum(j*F[j]*E[n-j] for j in range(1,n+1))/n))
    def gauss(polynomial):
        answer=0
        for (a,),v in S.Poly(polynomial,u).terms():
            if a%2==0: answer+=v*(S.factorial2(a-1) if a else 1)/B**(a//2)
        return S.cancel(answer)
    require(gauss(E[1])==gauss(E[3])==0, "odd Gaussian coefficients")
    D1=gauss(E[2]); D2=gauss(E[4])
    c1=S.cancel(D1.subs({l:0,r:0})); c2=S.cancel(D2.subs({l:0,r:0}))
    V1=S.cancel(D1-c1)
    V2=S.cancel(D2-c2-c1*V1)

    # Derive u1,u2 from offsets A_i=odd_i-r+U, where U=sum of r uniforms.
    # Uniform root mean l, variance (l^2-1)/3, distinct-pair covariance
    # -(l^2-1)/(3(l-1)); U has mean r/2 and variance r/12.
    root_mean=l
    root_pair=S.cancel(l*l-(l*l-1)/(3*(l-1)))
    shift_mean=-r/2
    shift_second=r*r/4+r/12
    pair_offset=S.expand(root_pair+2*root_mean*shift_mean+shift_second)
    op1=S.expand((l-r)*(root_mean+shift_mean))
    op2=S.expand((l-r)*(l-r-1)*pair_offset/2)
    # Generate the finite-product logarithms, then exponentiate to second order.
    def two_from_log(a,b): return S.cancel(a),S.cancel(b+a*a/2)
    df=two_from_log(S.summation((2*q+1)/2,(q,0,l-1)),S.summation((2*q+1)**2/8,(q,0,l-1)))
    fall=two_from_log(-S.summation(q,(q,0,r-1)),-S.summation(q*q/2,(q,0,r-1)))
    # Each pair lists epsilon and epsilon^2 in a factor normalized to constant 1.
    factors=[(-l,0),df,(mu*op1,mu*mu*op2),(mu*fall[0],mu*mu*fall[1]),(mu*V1,mu*mu*V2)]
    product=[S.Integer(1),S.Integer(0),S.Integer(0)]
    for a,b in factors:
        product=[product[0],product[1]+a*product[0],product[2]+a*product[1]+b*product[0]]
    A1=S.cancel(product[1]); A2=S.cancel(product[2])

    # Direct bivariate PGFs. beta=1/2 gives principal gamma_l, beta=1 gives
    # opposite-endpoint geometric weights. Subtract the l=0 atom after evaluation.
    # We differentiate q^(-beta) as a sum of q-powers represented by rational
    # functions, finally multiply by t^beta. This avoids artificial radicals.
    base=1-s*s*x*(1-s+s*y)
    @lru_cache(None)
    def mom(a,b,beta):
        G=base**(-beta)
        for _ in range(a): G=x*S.diff(G,x)
        for _ in range(b): G=y*S.diff(G,y)
        G=S.expand(G)
        # Each term at x=y=1 has t^(-beta-integer), so divide out sqrt analytically.
        # powdenest(force) is legitimate for 0<s<1 (our domain).
        ans=S.powsimp((t**beta)*G.subs({x:1,y:1}),force=True)
        ans=S.simplify(ans)
        ans=S.cancel(ans)
        if a==0 and b==0: ans-=t**beta
        return ans

    def weighted(polynomial,beta=S.Rational(1,2)):
        terms=S.Poly(S.expand(polynomial),l,r).terms()
        answer=0
        for (a,b),value in terms:
            if value!=0: answer+=value*mom(a,b,beta)
        return S.cancel(answer)
    # normalized principal sum M(P)=sqrt(t)*sum a0 P.
    R0=S.sqrt(t)
    g0=S.cancel(-s/S.diff(alpha,s)/t) # R0'/R0
    require(S.simplify(Da(R0)/R0-g0)==0, "leading logarithmic derivative")
    delta=alpha*l-r
    B1=s*s/(2*t)
    r1=S.cancel(-weighted(A1+delta*g0)-B1)

    # Exact expansion of R(N-l,m-r)/R0 through epsilon^2, excluding new r2.
    # alpha' = alpha+delta*epsilon+l*delta*epsilon^2+...
    # R0(alpha')/R0 = 1+g0*delta*eps+[g0*l*delta+(g0'+g0^2)*delta^2/2]*eps^2.
    # R1(alpha')/[(N-l)R0] supplies r1*eps+[l*r1+delta*(r1'+g0*r1)]*eps^2.
    shift1=r1+delta*g0
    shift2=l*r1+delta*(Da(r1)+g0*r1)+l*delta*g0+delta*delta*(Da(g0)+g0*g0)/2
    known_second=S.cancel(shift2+A1*shift1+A2)
    # Opposite endpoint: p_j monic, next coefficient determined by recurrence.
    # q_j-q_(j-1)=(2j-2)+j = 3j-2, q_0=0.
    a=S.symbols('a',integer=True,positive=True)
    p_top=S.summation(3*a-2,(a,1,l))
    require(S.expand(p_top-(3*l*l-l)/2)==0, "first top coefficient")
    # Multiplication by k^l is E(m-r+U)^(l-r) binom(l,r),
    # hence first relative coefficient -(l-r)r/2.
    mono1=-(l-r)*r/2
    opposite_first=S.cancel(df[0]+mu*(mono1+fall[0]+V1)+p_top*mu*(1-s))
    # weighted(_,1)=t*sum geometric joint weights, rather than sum itself.
    B2=S.cancel(weighted(opposite_first,S.Integer(1))/(2*t))
    r2=S.cancel(-weighted(known_second)-B2)

    # Diagonal multiplication: factorial correction, saddle in powers 1/n,
    # connected quotient in powers 1/(2n). Stirling logarithm has no n^-2 term.
    F1=S.Rational(1,48)-S.Rational(1,24)-S.Rational(2,12)
    F2=F1*F1/2
    b1_fun=S.cancel(F1+c1+r1/2)
    b2_fun=S.cancel(F2+c2+r2/4+F1*c1+(F1+c1)*r1/2)
    s0=(1+S.sqrt(17))/8
    b1=S.radsimp(S.simplify(b1_fun.subs(s,s0)))
    b2=S.radsimp(S.simplify(b2_fun.subs(s,s0)))


    # Exact target formulas are checked only after the regeneration above.
    expected_r1=(s**4+6*s**3+7*s**2+3*s+4)/(4*(s-1)*(s+1)*(s+2)**2)
    expected_r2=(s**10+14*s**9+22*s**8-218*s**7-1295*s**6-3068*s**5-3675*s**4-2402*s**3-1160*s**2-500*s-4)/(32*s*(s-1)**2*(s+1)**2*(s+2)**5)
    expected_c2=(s**12-14*s**11+759*s**10+1574*s**9-1079*s**8-4386*s**7-1346*s**6+4410*s**5+4128*s**4-368*s**3-1871*s**2-576*s+64)/(288*(s-1)**2*(s+1)**2*(s+2)**6)
    expected_B2=(s**4+9*s**3+13*s**2+3*s+4)/(4*(s-1)**2*(s+1)**2*(s+2)**2)
    expected_b1=-S.Rational(989,2176)-S.Rational(907,36992)*S.sqrt(17)
    expected_b2=-S.Rational(30800095,80494592)-S.Rational(3912441,80494592)*S.sqrt(17)
    for actual, expected in ((r1,expected_r1),(r2,expected_r2),(c2,expected_c2),(B2,expected_B2),(b1,expected_b1),(b2,expected_b2)):
        require(S.simplify(actual-expected)==0, 'independent target coefficient comparison')
    require(S.cancel(A1.subs({l:0,r:0}))==0 and S.cancel(A2.subs({l:0,r:0}))==0, 'kernel zero-shift normalization')
    require(S.cancel(known_second.subs({l:0,r:0}))==0, 'zero-atom rationality cancellation')
    lambda1=S.simplify(b1+S.Rational(1,12))
    lambda2=S.simplify(b2-b1*b1/2)
    # All data are typed exact values: ascending polynomial coefficients and
    # field pairs a+b*sqrt(17). No symbolic-expression parser is needed on replay.
    return {
        'field_radicand':17,
        'rational_functions':{name:rational_function(value,s) for name,value in
            [('r1',r1),('r2',r2),('D1',c1),('D2',c2),('B1',B1),('B2',B2)]},
        'diagonal':{'b1':quadratic(b1),'b2':quadratic(b2),
                    'factorial1':str(F1),'factorial2':str(F2),
                    'ratio2':quadratic(r2.subs(s,s0)/4),
                    'saddle2':quadratic(c2.subs(s,s0)),
                    'lambda1':quadratic(lambda1),'lambda2':quadratic(lambda2)},
        'checks':{'target_equalities':6,'odd_gaussian_zeros':2,
                  'kernel_zero_shift_zeros':2,'residual_zero_atom':1,
                  'normalized_moments_generated':mom.cache_info().currsize}}


if __name__ == '__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2,allow_nan=False))
