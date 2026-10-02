"""Independent direct checks of deficit polynomials and Poisson sum."""
from pathlib import Path
import sympy as s
import json
m,t,B,L1,L2,L3,L4=s.symbols('m t B L1 L2 L3 L4')
phi=t*(1-t**3)**(-s.Rational(1,3))
Q=(1-(m+1)*t**3/3)*(1-t**3)**(-s.Rational(2,3))*s.exp(B/t*((1-t**3)**s.Rational(1,3)-1)+L1*(phi-t)+L2*(phi**2-t**2)+L3*(phi**3-t**3)+L4*(phi**4-t**4))
Q=s.series(Q,t,0,5).removeO().expand()
P=[m+1]
for r in range(1,5):
    forcing=-s.series(Q*sum(P[i].subs(m,m-1)*phi**i for i in range(r)),t,0,r+1).removeO().expand().coeff(t,r)
    d=s.degree(forcing,m)+2 if forcing!=0 else 1
    coeff=s.symbols('a:'+str(d+1)); p=sum(a*m**i for i,a in enumerate(coeff))
    eq=s.expand(p.subs(m,m+1)-2*p+p.subs(m,m-1)-forcing)
    sol=s.solve(s.Poly(eq,m).all_coeffs()+[p.subs(m,0),p.subs(m,1)],coeff,dict=True)
    assert len(sol)==1
    P.append(s.factor(p.subs(sol[0])))
    print('P',r,P[-1])
rs=[]
for p in P:
    poly=s.Poly(s.cancel(p/(m+1)),m)
    expectation=sum(co*s.bell(k,s.Rational(1,2)) for (k,),co in poly.terms())
    rs.append(s.factor(expectation))
ratio=sum(rr*t**r for r,rr in enumerate(rs))
logratio=s.series(s.log(ratio),t,0,5).removeO().expand()
# v=n+1, use t=v^(-1/3) to compare the factorial-normalized total.
phiv=t*(1-t**3)**(-s.Rational(1,3))
ls=[L1,L2,L3,L4]
leaflog=s.series(-s.Rational(2,3)*s.log(1-t**3)+B/t*((1-t**3)**s.Rational(1,3)-1)+sum(a*phiv**r for r,a in enumerate(ls,1))+logratio.subs(t,phiv),t,0,5).removeO().expand()
report={'P':list(map(str,P)), 'r':list(map(str,rs)), 'log_ratio':str(logratio),'leaf_factorial_log':str(leaflog)}
Path(__file__).with_name('total-transfer-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
