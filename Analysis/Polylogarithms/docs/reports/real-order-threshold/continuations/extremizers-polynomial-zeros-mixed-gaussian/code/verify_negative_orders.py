"""Independent exact and numerical checks for negative Gaussian outer orders.

Exact SymPy calculations derive q_2, q_3, q_5 from z*d/dz, derive the
beta/eta combinations from Leibniz's rule, and verify the b=1 values.
The q_5 root count is checked by reciprocal-polynomial reduction and Sturm
counting.  Decimal b_2,b_3 values and Mellin residuals are diagnostics only;
the existence, uniqueness and simplicity proof is in the article.
"""
from pathlib import Path
from fractions import Fraction
import json, time
import sympy as s
import mpmath as mp

BASE=Path(__file__).resolve().parents[1]
START=time.monotonic()
z=s.Symbol('z')
y=s.Symbol('y',real=True)
t=s.Symbol('t',real=True)
b=s.Symbol('b',real=True)
B=s.Function('beta_D')
E=s.Function('eta_D')


def exact_derivations():
    initial=z**2/((1-z)*(1-z*y))
    derivative=initial
    kernels={}
    for j in range(6):
        if j in (2,3,5):
            at_i=derivative.subs(z,s.I)
            at_minus_i=derivative.subs(z,-s.I)
            kernels[j]=s.factor(s.cancel((at_i-at_minus_i)/(2*s.I)))
        derivative=s.factor(z*s.diff(derivative,z))
    expected={
        2:(1+y)*(y**4+6*y**2-3)/(2*(1+y**2)**3),
        3:-(1+y)*(y**4-22*y**2+1)/(1+y**2)**4,
        5:-(1+y)*(y**8-236*y**6+1446*y**4-236*y**2+1)/(1+y**2)**6}
    assert all(s.cancel(kernels[j]-expected[j])==0 for j in kernels)

    # Li_{-j}(i), calculated from the rational Li_0 rather than a table.
    li=z/(1-z)
    single_values=[]
    for j in range(6):
        single_values.append(s.simplify(li.subs(z,s.I)))
        li=s.factor(z*s.diff(li,z))
    combinations={}
    for m in (2,3):
        combination=0
        for j in range(m+1):
            order=b-m+j
            real_part=s.re(single_values[j])
            imag_part=s.im(single_values[j])
            combination+=s.binomial(m,j)*(real_part*B(order)
                            -imag_part*2**(-order)*E(order))
        combinations[m]=s.expand(combination)
    target2=(-B(b-2)-2*B(b-1)-2**(2-b)*E(b-2)+2**(-b)*E(b))/2
    target3=(2*B(b)-B(b-3)-3*B(b-2)-2**(3-b)*E(b-3)
             +3*2**(1-b)*E(b-1))/2
    assert s.simplify(combinations[2]-target2)==0
    assert s.simplify(combinations[3]-target3)==0

    # b=1, checked by rational-kernel integration and independent
    # differentiation of Li_{1,1}(z,1)=log(1-z)^2/2.
    exact_at_one={2:-s.Rational(3,4)+s.log(2)/4,
                  3:1+s.pi/4,
                  5:-s.Rational(15,2)-2*s.pi}
    integrated={j:s.integrate(kernels[j],(y,0,1)) for j in kernels}
    assert all(s.simplify(integrated[j]-exact_at_one[j])==0 for j in kernels)
    log_derivative=s.log(1-z)**2/2
    from_logs={}
    for j in range(1,7):
        log_derivative=s.diff(log_derivative,z)*z
        m=j-1
        if m in kernels:
            val=s.expand_complex(log_derivative.subs(z,s.I))
            from_logs[m]=s.simplify(s.im(val))
            assert s.simplify(from_logs[m]-exact_at_one[m])==0

    beta_eta_values={B(1):s.pi/4,E(1):s.log(2)}
    for j in range(3):
        beta_eta_values[B(-j)]=s.im(single_values[j])
        beta_eta_values[E(-j)]=-s.re(single_values[j])/s.Integer(2)**j
    for m in (2,3):
        result=combinations[m].subs(b,1).subs(beta_eta_values)
        assert s.simplify(result-exact_at_one[m])==0

    # q_5: after t=y^2 its numerator is reciprocal.
    P=t**4-236*t**3+1446*t**2-236*t+1
    reciprocal=t**2*((t+1/t)**2-236*(t+1/t)+1444)
    assert s.expand(P-reciprocal)==0
    vminus=118-8*s.sqrt(195)
    vplus=118+8*s.sqrt(195)
    v=s.Symbol('v')
    assert s.expand((v-vminus)*(v-vplus)-(v**2-236*v+1444))==0
    # vminus>2 follows from 116>0 and 116^2>64*195.
    assert 116**2-64*195==976>0
    q5_count=int(s.Poly(P,t).count_roots(0,1))
    assert q5_count==2
    counts={2:int(s.Poly(t**2+6*t-3,t).count_roots(0,1)),
            3:int(s.Poly(t**2-22*t+1,t).count_roots(0,1)),5:q5_count}
    assert counts[2]==counts[3]==1
    report={
        'method':'Exact SymPy differentiation, simplification and integration',
        'kernel_initial':str(initial),
        'derived_kernels':{str(j):str(q) for j,q in kernels.items()},
        'Li_negative_at_i':[str(q) for q in single_values],
        'beta_eta_combinations':{str(j):str(q) for j,q in combinations.items()},
        'exact_b_equals_one':{str(j):str(q) for j,q in exact_at_one.items()},
        'b_equals_one_checks':['rational-kernel integration',
                              'differentiated log(1-z)^2/2',
                              'beta/eta specializations at m=2,3'],
        'kernel_endpoint_values':{str(j):{'at_zero':str(q.subs(y,0)),
                                          'at_one':str(q.subs(y,1))}
                                  for j,q in kernels.items()},
        'Sturm_root_counts_in_0_1':{str(j):n for j,n in counts.items()},
        'q5_reciprocal_proof':{
            'polynomial_in_t_equals_y_squared':str(P),
            'identity':'P(t)=t^2*((t+1/t)^2-236*(t+1/t)+1444)',
            'two_v_values':[str(vminus),str(vplus)],
            'exact_positive_square_difference':976,
            'argument':'Both v values exceed 2. For each v, t+1/t=v has exactly one simple root in (0,1). The two v values differ, so q5 has exactly two simple zeros there.',
            'kernel_signs_as_y_increases':['negative','positive','negative']}}
    return kernels,report


def numerical_diagnostics(kernels):
    mp.mp.dps=85
    beta=lambda x:mp.dirichlet(x,[0,1,0,-1])
    eta=mp.altzeta
    g2=lambda x:(-beta(x-2)-2*beta(x-1)-2**(2-x)*eta(x-2)
                 +2**(-x)*eta(x))/2
    g3=lambda x:(2*beta(x)-beta(x-3)-3*beta(x-2)-2**(3-x)*eta(x-3)
                 +3*2**(1-x)*eta(x-1))/2
    roots={2:mp.findroot(g2,(mp.mpf('0.25'),mp.mpf('0.75'))),
           3:mp.findroot(g3,(mp.mpf('2'),mp.mpf('3')))}
    kernel_roots={2:mp.sqrt(-3+2*mp.sqrt(3)),
                  3:mp.sqrt(11-2*mp.sqrt(30))}
    records={}
    for j,formula in [(2,g2),(3,g3)]:
        b0=roots[j]
        q=s.lambdify(y,kernels[j],'mpmath')
        tau=-mp.log(kernel_roots[j])
        # t=u^16 removes the integrable endpoint singularity for b2.
        power=16
        def integrand(u):
            if not u:return mp.mpf(0)
            tt=u**power
            yy=mp.exp(-tt)
            return power*u**(power*b0-1)*yy*q(yy)/mp.gamma(b0)
        mellin=mp.quad(integrand,[0,tau**(mp.mpf(1)/power),1,2,mp.inf])
        formula_residual=formula(b0)
        derivative=mp.diff(formula,b0)
        assert abs(mellin)<mp.mpf('1e-70')
        assert abs(formula_residual)<mp.mpf('1e-75')
        assert derivative<0
        records[str(j)]={
            'b_root':mp.nstr(b0,80),
            'Dirichlet_formula_residual':mp.nstr(formula_residual,15),
            'independent_Mellin_residual':mp.nstr(mellin,15),
            'numerical_derivative_at_root':mp.nstr(derivative,40),
            'sample_below':{'b':mp.nstr(b0/2,20),
                            'value':mp.nstr(formula(b0/2),25)},
            'sample_above':{'b':mp.nstr(b0+1,20),
                            'value':mp.nstr(formula(b0+1),25)}}
    vvalues=[118+8*mp.sqrt(195),118-8*mp.sqrt(195)]
    q5roots=[mp.sqrt(2/(v+mp.sqrt(v*v-4))) for v in vvalues]
    return {'status':'Decimal diagnostics, not root enclosures or a uniqueness certificate',
            'decimal_working_precision':mp.mp.dps,
            'mellin_evaluation':'t=u^16 in the gamma integral; quadrature without a certified error bound',
            'roots':records,
            'q5_kernel_roots_in_y':[mp.nstr(r,60) for r in q5roots]}


if __name__=='__main__':
    kernels,exact=exact_derivations()
    print('Exact rational-kernel, beta/eta and reciprocal-root checks passed',flush=True)
    numerical=numerical_diagnostics(kernels)
    result={'exact_checks':exact,'numerical_diagnostics':numerical,
            'dependencies':{'sympy':s.__version__,'mpmath':mp.__version__},
            'elapsed_seconds':round(time.monotonic()-START,3)}
    path=BASE/'data/negative_orders_diagnostics.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'result':'All checks passed',
                      'b2':numerical['roots']['2']['b_root'],
                      'b3':numerical['roots']['3']['b_root'],
                      'q5_kernel_roots':numerical['q5_kernel_roots_in_y'],
                      'elapsed_seconds':result['elapsed_seconds']},indent=2))
