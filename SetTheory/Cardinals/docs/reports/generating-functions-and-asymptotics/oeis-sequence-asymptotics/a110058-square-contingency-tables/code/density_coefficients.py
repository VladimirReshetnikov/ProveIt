"""Fixed symbolic density calculation with independent Gaussian factorization.

The input is a formal symbol, not a numerical density. Degree eight and diagram
cost three are the only supported truncations. This proves finite rational
identities, not compact-uniform analytic bounds or finite-density certificates.
"""
import sys
sys.dont_write_bytecode=True
from collections import Counter
import sympy as s
from common import expected_specifications, require
from formal_factorization import cumulant


def check_density():
    lam,u,t=s.symbols('lambda u t')
    A=lam*(1+lam)/2
    # Finite composition for -log(1-lambda*(exp(t)-1)), through degree eight.
    exp_minus_one=sum(t**j/s.factorial(j) for j in range(1,9))
    geometric=0; power=s.Integer(1)
    for j in range(1,9):
        product=s.Poly(s.expand(power*exp_minus_one),t)
        power=sum(value*t**degree[0] for degree,value in product.terms() if degree[0]<=8)
        geometric+=lam**j*power/j
    geometric=s.Poly(s.expand(geometric),t)
    kappas={d:s.expand(geometric.coeff_monomial(t**d)*s.factorial(d)) for d in range(1,9)}
    # Additional independent differential recurrence and reflection checks.
    require(kappas[1]==lam and kappas[2]==s.expand(lam*(1+lam)),'initial geometric cumulants')
    for d in range(1,8):
        require(s.expand(kappas[d+1]-lam*(1+lam)*s.diff(kappas[d],lam))==0,'density cumulant recurrence')
    for d in range(2,9):
        require(s.expand(kappas[d].subs(lam,-1-lam)-(-1)**d*kappas[d])==0,'density reflection identity')
    coeff={0:s.Integer(0),-1:s.Integer(0),-2:s.Integer(0)}
    rows=[]
    for ds in expected_specifications():
        E=sum(ds)//2
        weight=s.Integer((-1)**E)
        for d in ds:weight*=kappas[d]/s.factorial(d)
        for count in Counter(ds).values():weight/=s.factorial(count)
        weight/=A**E
        gaussian=cumulant(ds)
        contributions={p:s.cancel(weight*s.Rational(gaussian.get(p,0))) for p in coeff}
        for p,value in contributions.items():coeff[p]+=value
        rows.append({'degrees':list(ds),'contributions':{str(p):str(s.factor(v)) for p,v in contributions.items()}})
    expected={0:s.Rational(1,3)-1/(6*u),-1:-s.Rational(3,2),
              -2:s.Rational(1171,180)+11/(12*u)+1/(60*u*u)+1/(180*u**3)}
    for p,value in coeff.items():
        require(s.cancel(value-expected[p].subs(u,lam*(1+lam)))==0,'symbolic density coefficient mismatch')
    at_one={str(p):str(value.subs(u,2)) for p,value in expected.items()}
    require(at_one=={'0':'1/4','-1':'-3/2','-2':'223/32'},'density-one reduction mismatch')
    return {'status':'PASS','max_geometric_degree':8,'max_diagram_cost':3,
            'geometric_cumulants':{str(d):str(s.factor(value)) for d,value in kappas.items()},
            'coefficient_polynomials':{str(p):str(value) for p,value in expected.items()},
            'density_one_coefficients':at_one,'rows':rows,
            'scope':'Finite exact identities with formal u=lambda*(1+lambda); no numerical-density or analytic uniformity certificate.'}


def check_cm_comparison():
    """Exact finite Stirling algebra in the stated comparison normalization.

    The omitted Stirling remainders and eventual inequalities are analytic
    statements in the article, not consequences of this finite computation.
    """
    lam,u,t=s.symbols('lambda u t')
    L,log_lam,log_one_plus_lam,log_two_pi=s.symbols('L log_lambda log_one_plus_lambda log_2pi')
    def gamma_series(q,log_q,k):
        scale=t**(-k)
        main=(q*scale-s.Rational(1,2))*(log_q+k*L)-q*scale+log_two_pi/2
        correction=sum(s.bernoulli(2*j)/(2*j*(2*j-1)*(q*scale)**(2*j-1)) for j in (1,2))
        return main+correction
    def binomial_series(k):
        return (gamma_series(1+lam,log_one_plus_lam,k)
                -gamma_series(lam,log_lam,k)-(log_lam+k*L)
                -gamma_series(s.Integer(1),s.Integer(0),k))
    b1=-(1+1/u)/12
    b3=(1+3/u**2+1/u**3)/360
    one_binomial=s.expand(binomial_series(1))
    for power,value in ((1,b1),(3,b3)):
        require(s.cancel(one_binomial.coeff(t,power)-value.subs(u,lam*(1+lam)))==0,'binomial Stirling coefficient mismatch')
    entropy=(1+lam)*log_one_plus_lam-lam*log_lam
    log_G=entropy/t**2-(1/t-s.Rational(1,2))*(log_two_pi+log_lam+log_one_plus_lam)-(1/t-1)*L
    adjustment=(1/t-1)*(t-t*t/2+t**3/3-t**4/4)-s.Rational(1,2)
    comparison=s.expand(2*binomial_series(1)/t-binomial_series(2)+adjustment-log_G)
    require(comparison.coeff(t,-2)==0 and comparison.coeff(t,-1)==0,'Stirling leading cancellation')
    expected={0:s.Rational(1,3)-1/(6*u),1:-s.Rational(3,2),
              2:s.Rational(83,90)+1/(12*u)+1/(60*u**2)+1/(180*u**3)}
    for power,value in expected.items():
        require(s.cancel(comparison.coeff(t,power)-value.subs(u,lam*(1+lam)))==0,'CM normalization coefficient mismatch')
    P2=s.Rational(1171,180)+11/(12*u)+1/(60*u**2)+1/(180*u**3)
    delta=s.factor(2*(P2-expected[2]))
    require(s.cancel(delta-(s.Rational(67,6)+5/(3*u)))==0,'CM delta coefficient mismatch')
    return {'status':'PASS',
            'normalization':'T(n,s)=binom(n+s-1,s)^(2*n)/binom(n^2+n*s-1,n*s)*(1+1/n)^(n-1)*exp(-1/2+Delta/(2*n))',
            'binomial_stirling_coefficients':{'b1':str(b1),'b3':str(s.expand(b3)),'g2':str(s.expand(2*b3-b1))},
            'log_comparison_over_G_coefficients':{str(-p):str(v) for p,v in expected.items()},
            'Delta_n_minus_1_coefficient':str(s.expand(delta)),
            'density_one_Delta_n_minus_1_coefficient':str(delta.subs(u,2)),
            'scope':'Exact finite Stirling coefficient comparison; analytic remainders and eventual conjecture range require the article.'}
