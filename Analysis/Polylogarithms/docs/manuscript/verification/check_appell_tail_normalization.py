"""Independent finite residue/tail audit for the all-degree Gamma-Appell bridge."""
from pathlib import Path
import json,sympy as S,time
V=Path(__file__).resolve().parent;mmax=9
h=S.symbols('h1:10');z={j:S.Symbol('z'+str(j)) for j in range(2,11)};a={j:S.Symbol('A'+str(j)) for j in range(2,11)};v=S.Symbol('v');y=S.Symbol('y');t=S.Symbol('t');g=S.Symbol('gamma')
# Coefficients of exp(h1*t + sum(z_j*t^j/j)), via t differentiation.
Phi=[S.Integer(1)]
for m in range(1,mmax+1):Phi.append(S.expand(sum((h[0] if j==1 else z[j])*Phi[m-j]/S.factorial(m-j) for j in range(1,m+1))*S.factorial(m-1)))
e=[S.Integer(1)]
for r in range(1,mmax):e.append(S.expand(sum((-1)**(j-1)*h[j-1]*e[r-j] for j in range(1,r+1))/r))
# Laurent coefficients using exact sparse convolution, no source compiler.
def mul(p,q,cap):
 out={}
 for i,c in p.items():
  for j,d in q.items():
   if i+j<=cap:out[i+j]=S.expand(out.get(i+j,0)+c*d)
 return out
even_rules={z[2*r]:(-1)**(r+1)*S.bernoulli(2*r)*2**(2*r-1)*6**r*z[2]**r/S.factorial(2*r) for r in range(2,6)}
records=[];defects={};started=time.time()
for m in range(2,mmax+1):
 psi={-1:S.Integer(-1),0:h[0]}|{r-1:h[r-1]+(-1)**r*z[r] for r in range(2,m+1)}
 # Every future negative factor lowers exponent at most one, so this cap
 # retains all terms needed for a simple pole in each power.
 powers=[{0:S.Integer(1)}]
 for k in range(1,m+1):powers.append(mul(powers[-1],psi,m-k-1))
 scalar=S.Poly(Phi[m],h[0]);res=S.expand(sum(c*powers[k[0]].get(-1,0) for k,c in scalar.terms()))
 delta=S.expand(res+S.factorial(m)*e[m-1]);tail=S.expand(delta.subs({h[j-1]:z[j]-a[j] for j in range(2,m+1)},simultaneous=True));tail=S.expand(tail.xreplace(even_rules));assert S.expand(tail.subs({q:0 for q in a.values()}))==0
 if m<=3:assert tail==0
 else:assert S.Poly(tail,h[0],*a.values()).total_degree()<=m-3
 diff=S.expand(tail.subs(h[0],h[0]+v)-tail.subs({a[j]:a[j]+v**j for j in range(2,m+1)},simultaneous=True))
 for ex,c in S.Poly(diff,v,h[0],*a.values()).terms():
  if c==0:continue
  assert ex[0]>=1 and (ex[0]>=2 or sum(ex[2:])>=1)
  assert sum(ex[1:])<=m-4
 defects[m]=tail;records.append(dict(degree=m,tail_ideal=True,degree_bound=True,finite_difference_convergence_rule=True,defect=str(tail)));print('degree',m,'PASS',flush=True)
assert defects[4]==-4*a[3]
assert S.expand(defects[5]-(5*a[2]**2-20*z[2]*a[2]-20*h[0]*a[3]+25*a[4]))==0
# Lower normalized moments, checked against canonical raw formulas.
l1,l2,l3,l4,om,d22,d31o,d31i,zp2,zp3,zp4=S.symbols('lambda1 lambda2 lambda3 lambda4 Omega D22 D31outer D31inner zp2 zp3 zp4');gam1=S.Symbol('gamma1')
c=[S.Integer(1)]
for j in range(1,6):c.append(S.expand((g*c[j-1]+sum((-1)**(r+1)*z[r]*c[j-r] for r in range(2,j+1)))/j))
Q={0:S.Integer(1),1:S.Integer(0),2:2*gam1-2*z[2],3:3*z[2]-6*l2-6*g*gam1,4:12*z[3]-12*g*z[2]+18*z[4]+4*zp3-24*l3+24*g*l2+12*(g*g-z[2])*gam1,5:30*g*g*z[2]-60*g*z[3]+S.Rational(35,3)*z[4]-120*l4+120*g*l3+60*(z[2]-g*g)*l2-20*(g**3-3*g*z[2]+z[3])*gam1+10*om+10*z[2]*zp2-20*g*zp3}
P=[S.Integer(1)]
for j in range(1,6):P.append(S.expand(sum((y+g if r==1 else z[r])*P[j-r]/S.factorial(j-r) for r in range(1,j+1))*S.factorial(j-1)))
expected={2:2*(c[2]+gam1),3:6*(c[3]-l2)+3*z[2],4:24*(c[4]-l3)+12*z[3]+4*zp3,5:120*(c[5]-l4)+S.Rational(260,3)*z[4]+10*z[2]*zp2+10*d22+20*d31o-20*d31i-20*zp4}
lower=[]
for j in range(2,6):
 value=S.expand(sum(coeff*Q[ex[0]] for ex,coeff in S.Poly(P[j],y).terms()));value=value.subs(om,-2*z[3]*gam1+d22+2*d31o-2*d31i-2*zp4);r=S.Poly(S.expand(value-expected[j]),z[2]);rem=S.rem(r,S.Poly(z[2]**2-S.Rational(5,2)*z[4],z[2])).as_expr();assert S.expand(rem)==0;lower.append(j)
# Check formal transport independently from the tail compiler.
u=S.symbols('u0:9');prior=json.loads((V/'ibp-normal-forms-exact.json').read_text());N={0:S.Integer(1),1:u[0],2:u[0]**2,3:u[0]**3}|{int(k):S.sympify(text,locals={str(q):q for q in u}) for k,text in prior['normal_forms'].items()};transport=0
for m in range(2,9):
 assert S.expand(S.diff(N[m],u[0])-m*N[m-1])==0
 # Construct Gamma-Appell scalar polynomials through degree eight.
 ext=[S.Integer(1)]
 for j in range(1,m+1):ext.append(S.expand(sum((y+g if r==1 else z[r])*ext[j-r]/S.factorial(j-r) for r in range(1,j+1))*S.factorial(j-1)))
 left=S.expand(sum(S.binomial(m,k)*ext[m-k].subs(y,0)*N[k] for k in range(m+1)));right=S.expand(sum(S.binomial(m,j)*ext[j].subs(y,u[0])*N[m-j].subs(u[0],0) for j in range(m+1)));assert S.expand(left-right)==0;transport+=1
corrupt=S.expand(sum(coeff*Q[ex[0]] for ex,coeff in S.Poly(P[5],y).terms())).subs(om,d22+2*d31o-2*d31i-2*zp4)
control=S.rem(S.Poly(S.expand(corrupt-expected[5]),z[2]),S.Poly(z[2]**2-S.Rational(5,2)*z[4],z[2])).as_expr();assert S.expand(control-20*z[3]*gam1)==0 and control!=0
out=dict(status='PASS',degrees=[2,mmax],records=records,lower_moment_coordinate_checks=lower,formal_transport_checks=transport,missing_Stieltjes_control_detected=True,elapsed_seconds=round(time.time()-started,3),scope='Independent finite Laurent convolution, tail ideal/degree/difference checks and exact conversions to the canonical raw moments. Infinite all-degree identities and convergence rest on the manuscript proof; formal zero checks do not assert arithmetic independence.')
(V/'appell-tail-normalization-exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
