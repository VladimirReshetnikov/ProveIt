import sympy as S, json, argparse, sys
from pathlib import Path
parser=argparse.ArgumentParser(description="Finite exact coefficient generator for the A330498 expansion")
parser.add_argument("--order",type=int,default=4,help="number of P_j polynomials, starting with P_0")
parser.add_argument("--output",type=Path,help="write JSON here; otherwise stdout")
args=parser.parse_args()
if args.order<1:raise ValueError("--order must be positive")
s,z,u,M,b,t=S.symbols('s z u M b t', real=True)
I=S.I
J=args.order
B=1-S.log(1-M*(S.exp(t)-1))
cum=S.series(S.log(B),t,0,J+3).removeO().expand()
kappa={j:S.factor(cum.coeff(t,j)*S.factorial(j)) for j in range(1,J+3)}
print('cumulants computed',file=sys.stderr,flush=True)
E=sum(s**j*(kappa[j+2]/M*(I*u)**(j+2)/S.factorial(j+2)+z*kappa[j+1]/M*(I*u)**(j+1)/S.factorial(j+1)) for j in range(1,J))
w=S.series(S.exp(E)/(1+s*z),s,0,J).removeO().expand()
g=[]
for j in range(J):
 p=0
 for (r,),v in S.Poly(w.coeff(s,j),u).terms():
  p+=v*I**(-r)*(-1)**r*S.hermite_prob(r,z)
 g.append(S.factor(S.expand(p)))
 print('G',j,'computed',file=sys.stderr,flush=True)
R=sum(2*b*S.binomial(S.Rational(1,2),j+1)*z**(j+1)*s**j for j in range(1,J))
a=[S.Rational(1)]
for k in range(1,J):a.append(-a[-1]*S.Rational((2*k-1)**2,8*k))
amp=S.series((1+s*z)**S.Rational(-1,4)*S.exp(I*R)*sum(a[k]*(I*s/(2*b))**k*(1+s*z)**(-S.Rational(k,2)) for k in range(J)),s,0,J).removeO()
Q=S.Poly(S.expand(amp*sum(g[j]*s**j for j in range(J))),s)
P=[]
for j in range(J):
 p=0
 for (r,),v in S.Poly(Q.coeff_monomial(s**j),z).terms():p+=v*I**r*S.hermite_prob(r,b)
 p=S.factor(S.expand(p/I**j));P.append(p)
 print('P',j,'computed',file=sys.stderr,flush=True)
expected=(2*M**2-1)*b**3/12-b/2-1/(16*b)
if J>1 and S.simplify(P[1]-expected)!=0:raise ValueError('P1 mismatch')
obj={'cumulants':{str(k):str(v) for k,v in kappa.items()},'edgeworth':[str(x) for x in g],'P':[str(x) for x in P]}
serialized=json.dumps(obj,indent=2)+'\n'
if args.output:args.output.write_text(serialized)
else:print(serialized,end='')
