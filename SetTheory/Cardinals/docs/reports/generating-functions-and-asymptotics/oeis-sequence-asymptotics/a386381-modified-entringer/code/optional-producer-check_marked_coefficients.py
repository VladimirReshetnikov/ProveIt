import sympy as s,json
from pathlib import Path
t,u,r,lam=s.symbols('t u r lam')
V=s.series(r*s.cot(r*t/2),t,0,8).removeO()
h=[s.Integer(0),s.Integer(1)]
for k in range(6):
 h.append(s.expand((((k+1)**2+2*lam)*h[k+1]+lam*sum(V.coeff(t,j)*h[k-j] for j in range(1,k+1)))/((k+2)*(k+1))))
L=s.series(lam*V*sum(a*t**j for j,a in enumerate(h)),t,0,6).removeO()
R=1+sum(L.coeff(t,j)*(-1)**(j+1)*s.factorial(j)*u**(j+1)/s.prod(1-i*u for i in range(j+1)) for j in range(4))
R=s.series(R,u,0,5).removeO()
P=s.series(R/R.subs(lam,1),u,0,4).removeO()
logP=s.series(s.log(P),u,0,4).removeO()
mean=s.expand(s.diff(logP,lam).subs(lam,1));var=s.expand((s.diff(logP,lam,2)+s.diff(logP,lam)).subs(lam,1))
expected=[-2*lam,lam+2*lam**2,lam*(r**2-(1+2*lam)**2)/3]
for j in range(3):
 if s.expand(R.coeff(u,j+1)-expected[j])!=0:raise RuntimeError('Marked correction mismatch')
out={'unnormalized_relative':str(s.collect(s.expand(R),u)),'normalized_pgf_correction':str(s.collect(s.factor(P),u)),'log_pgf_correction':str(s.collect(s.expand(logP),u)),'mean_correction':str(mean),'variance_correction':str(var),'scope':'Symbolic coefficients only; uniform-complex-parameter theorem remains a separate analytic proof obligation'}
Path(__file__).with_name('marked_coefficients.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
