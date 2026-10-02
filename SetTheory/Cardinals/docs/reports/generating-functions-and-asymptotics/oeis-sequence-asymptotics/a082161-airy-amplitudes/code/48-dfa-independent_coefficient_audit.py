#!/usr/bin/env python3
"""Independent coefficient audit, using direct linear solves for P,Q,s.
Does not import the proposed formal_compacted.py or its inversion routine.
"""
import sympy as S
import json
x,e,a=S.symbols('x e a')
K=6
zero=(S.Integer(0),S.Integer(0))

def cut(z,n=K):
    return S.series(z,e,0,n+1).removeO().expand()

def diff(pair):
    p,q=pair
    return (S.diff(p,x)+2*(x+a)*q,p+S.diff(q,x))

def shift(pair,delta,n):
    result=[0,0]
    deriv=pair
    for k in range(n+1):
        mon=cut(delta**k,n)/S.factorial(k)
        result=[cut(result[i]+mon*deriv[i],n) for i in range(2)]
        deriv=diff(deriv)
    return result

A=cut((1-x*e**2+3*e**3)/(1+x*e**2-e**3))
B=cut(e**3*(1-x*e**2+e**3)/((1+x*e**2-e**3)*(1+x*e**2-3*e**3)))
profiles=[(S.Integer(1),S.Integer(0))]
scalars={2:a}
for m in range(3,K+1):
    # Compute forcing using only previous-order profiles and ratio coefficients.
    recurrence=[0,0]
    for j,pair in enumerate(profiles):
        for direction,weight in [(-1,A),(1,S.Integer(1))]:
            delta=cut((x+direction*e)*(1-e**3)**(-S.Rational(1,3))-x,m-j)
            shifted=shift(pair,delta,m-j)
            recurrence=[cut(recurrence[i]+weight*e**j*(1-e**3)**(-S.Rational(j,3))*shifted[i],m) for i in range(2)]
        if j+3<=m:
            ratio=lambda r: 2*(1+sum(s*e**t*(1-r*e**3)**(-S.Rational(t,3)) for t,s in scalars.items()))
            memory=cut(1/(ratio(1)*ratio(2)),m-j-3)
            delta=cut((x-e)*(1-3*e**3)**(-S.Rational(1,3))-x,m-j-3)
            shifted=shift(pair,delta,m-j-3)
            recurrence=[cut(recurrence[i]-B*memory*e**j*(1-3*e**3)**(-S.Rational(j,3))*shifted[i],m) for i in range(2)]
    current=[sum(e**j*p[i] for j,p in enumerate(profiles)) for i in range(2)]
    residual=[cut(recurrence[i]-2*(1+sum(s*e**t for t,s in scalars.items()))*current[i],m).coeff(e,m) for i in range(2)]
    k=m-2
    pp=S.symbols(f'p0:{2*k+1}'); qq=S.symbols(f'q0:{max(1,2*k-1)}'); scalar=S.Symbol('snew')
    P=sum(v*x**i for i,v in enumerate(pp)); Q=sum(v*x**i for i,v in enumerate(qq))
    lhs=[S.diff(P,x,2)+4*(x+a)*S.diff(Q,x)+2*Q-2*scalar+residual[0],2*S.diff(P,x)+S.diff(Q,x,2)+residual[1]]
    equations=[]
    for z in lhs:
        equations.extend(S.Poly(z,x).all_coeffs())
    equations.extend([Q.subs(x,0),(P+S.diff(Q,x)).subs(x,0)])
    unknowns=pp+qq+(scalar,)
    solutions=S.solve(equations,unknowns,dict=True)
    assert len(solutions)==1,(m,solutions)
    sol=solutions[0]
    assert all(v in sol for v in unknowns)
    profiles.append((S.factor(P.subs(sol)),S.factor(Q.subs(sol))))
    scalars[m]=S.factor(sol[scalar])

# Independently solve the finite-logarithm ratio using its exact difference.
h1,h2,h3=S.symbols('h1 h2 h3')
rho=scalars[3]
delta_log=3*a/e*(1-(1-e**3)**S.Rational(1,3))-rho*S.log(1-e**3)
for k,h in enumerate([h1,h2,h3],1):
    delta_log+=h*e**k*(1-(1-e**3)**(-S.Rational(k,3)))
log_target=S.log(1+sum(s*e**k for k,s in scalars.items()))
resid=cut(delta_log-log_target)
hsolution=S.solve([resid.coeff(e,k) for k in [4,5,6]],[h1,h2,h3],dict=True)[0]

# Boundary derivatives are computed directly from the normalized Airy ODE.
fseries=[S.Integer(0),S.Integer(1)]
for n in range(8):
    rhs=2*a*fseries[n]+(2*fseries[n-1] if n else 0)
    fseries.append(S.expand(rhs/((n+2)*(n+1))))
f=sum(v*x**n for n,v in enumerate(fseries))
endpoint=cut(sum(e**k*(P*f+Q*S.diff(f,x)).subs(x,e) for k,(P,Q) in enumerate(profiles))/e,3)
logs=cut(S.log(endpoint),3)+hsolution[h1]*e+hsolution[h2]*e**2+hsolution[h3]*e**3
z=S.symbols('z')
coeffs=[S.simplify(logs.coeff(e,k).subs(a,z/2**S.Rational(1,3))/2**S.Rational(k,3)) for k in range(1,4)]
expected=[53*z*z/S.Integer(90),623*z/S.Integer(432),S.Rational(3497,4480)-1304*z**3/S.Integer(42525)]
assert all(S.simplify(v-w)==0 for v,w in zip(coeffs,expected))
print(json.dumps({'s':{str(k):str(v) for k,v in scalars.items()},'profiles':[[str(p),str(q)] for p,q in profiles],'endpoint':str(endpoint),'logforward_n':list(map(str,coeffs))},indent=2))
