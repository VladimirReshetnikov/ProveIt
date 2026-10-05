"""Exact symbolic reconstruction of the marked saddle jets and first correction."""
from pathlib import Path
import sympy as s,json,time
ROOT=Path(__file__).resolve().parent;start=time.time();e,X,Y=s.symbols('e X Y');a=e*X;b=e*Y
w=s.S(0)
for j in range(1,5):
 c=s.symbols(f'w{j}');candidate=w+c*e**j
 expr=s.series(2*s.sinh(candidate)+4*s.exp(a)*s.sinh(b+2*candidate),e,0,j+1).removeO().expand().coeff(e,j)
 sol=s.solve(expr,c)
 if len(sol)!=1:raise RuntimeError(('implicit coefficient',j))
 w=s.expand(candidate.subs(c,sol[0]))
print('implicit jet',w,flush=True)
P=s.series(2*s.cosh(w)+2*s.exp(a)*s.cosh(b+2*w),e,0,5).removeO()
phase=s.series(s.log(P)-a/2,e,0,5).removeO().expand()
expected={2:X*X/s.Integer(8)+Y*Y/s.Integer(20),3:-s.Rational(3,200)*X*Y*Y,4:-X**4/s.Integer(192)-X*X*Y*Y/s.Integer(125)-s.Rational(41,60000)*Y**4}
for j,val in expected.items():
 if s.simplify(phase.coeff(e,j)-val)!=0:raise RuntimeError(('phase jet',j,phase.coeff(e,j),val))
# Amplitude derivative jets. The constant log(2pi) cancels in all ratios.
P2=s.series(P,e,0,3).removeO();pww=s.series(2*s.cosh(w)+8*s.exp(a)*s.cosh(b+2*w),e,0,3).removeO()
c0=s.series(s.cosh(b+2*w)+s.exp(-a)*s.cosh(w)/2,e,0,3).removeO();dc=s.expand(c0-s.Rational(3,2))
# Taylor derivatives of acosh at3/2 are2/sqrt5 and-12/(5sqrt5).
ac=s.acosh(s.Rational(3,2))+2*dc/s.sqrt(5)-6*dc*dc/(5*s.sqrt(5))
logamp=s.series(s.log(P2)-a-ac-s.log(pww/P2)/2,e,0,3).removeO().expand()
La=s.simplify(logamp.coeff(e,1).coeff(X,1));Laa=s.simplify(2*logamp.coeff(e,2).coeff(X,2));Lbb=s.simplify(2*logamp.coeff(e,2).coeff(Y,2))
Aa=La;Aaa=s.simplify(Laa+La*La);Abb=Lbb
for got,want in [(Aa,s.sqrt(5)/5-s.Rational(13,20)),(Aaa,s.Rational(367,400)-17*s.sqrt(5)/50),(Abb,s.Rational(59,500)-6*s.sqrt(5)/125)]:
 if s.simplify(got-want)!=0:raise RuntimeError(('amplitude jet',got,want))
# Direct nested-radical Puiseux calculation at equal weights.
x=s.symbols('x',positive=True);t=(1-x*x)/4;v=(-1+s.sqrt(9+4/t))/2;V=(-1-s.sqrt(9+4/t))/2
E=s.series(-(v-s.sqrt(v*v-4))*(V+s.sqrt(V*V-4))/(4*t),x,0,4).removeO().expand()
e1=s.simplify(E.coeff(x,1));e3=s.simplify(E.coeff(x,3));B1=s.simplify(s.Rational(3,8)-s.Rational(3,2)*e3/e1)
b1=s.simplify(B1-2*Aaa-5*Abb-s.Rational(3,5)*Aa-s.Rational(91,100));c1=s.simplify(b1/4-s.Rational(7,80))
if s.simplify(c1-13*(s.sqrt(5)-5)/50)!=0:raise RuntimeError('first correction')
out={'all_pass':True,'implicit_log_tau_jet':str(w),'phase_jets':{str(j):str(v) for j,v in expected.items()},'amplitude_Aa_over_A':str(Aa),'amplitude_Aaa_over_A':str(Aaa),'amplitude_Abb_over_A':str(Abb),'Puiseux_e1':str(e1),'Puiseux_e3':str(e3),'univariate_first_correction':str(B1),'basketball_correction_in_N':str(b1),'A215570_first_correction':str(c1),'seconds':time.time()-start};(ROOT/'jet_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
