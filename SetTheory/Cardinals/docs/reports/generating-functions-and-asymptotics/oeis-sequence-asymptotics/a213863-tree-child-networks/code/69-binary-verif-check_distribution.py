"""Independent distribution algebra from independently audited deficit polynomials."""
from pathlib import Path
import sympy as s
import json
m,t,B,u=s.symbols('m t B u')
d=json.loads(Path(__file__).with_name('total-transfer-order6-checks.json').read_text())
P=[s.sympify(a,locals={'m':m,'B':B}) for a in d['P']]
r=[s.sympify(a,locals={'B':B}) for a in d['r']]
q=s.series(1/sum(a*t**i for i,a in enumerate(r)),t,0,7).removeO().expand()
C=[s.factor(sum(s.cancel(P[i]/(m+1))*q.coeff(t,j-i) for i in range(j+1))) for j in range(7)]
def E(f,lam=s.Rational(1,2)):
    return s.simplify(sum(a*s.bell(k,lam) for (k,),a in s.Poly(s.expand(f),m).terms()))
assert E(C[0])==1 and all(E(c)==0 for c in C[1:])
TV=[s.factor(s.Rational(3,2)*q.coeff(t,j)) for j in range(1,7)]
# TV coefficient list omits the common factor exp(-1/2).
pgf=[s.factor(E(c,u/2)) for c in C[:4]]
mean=sum(E(m*c)*t**j for j,c in enumerate(C[:4]))
raw2=sum(E(m*m*c)*t**j for j,c in enumerate(C[:4]))
var=s.series(raw2-mean**2,t,0,4).removeO().expand()
assert s.simplify(C[2].subs(m,2)-7*B/72)==0
report={'correction_polynomials':list(map(str,C)),'normalization_mean_zero':True,'TV_coefficients_without_exp_minus_half':list(map(str,TV)),'PGF_polynomials_after_exp':list(map(str,pgf)),'mean_to_t3':str(mean),'variance_to_t3':str(var),'likelihood_at_m2_t2':str(C[2].subs(m,2))}
Path(__file__).with_name('distribution-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
