from pathlib import Path
import sympy as s,json
h,u,x=s.symbols('h u x');R=4
tr=lambda a:s.series(a,h,0,R+3).removeO().expand()
mu=[s.Integer(1)]+[tr(s.factorial(r)/s.prod(1+j*h*h for j in range(1,r+1))) for r in range(1,R+3)]
kappa=[s.Integer(0)]
for r in range(1,R+3):kappa.append(tr(mu[r]-sum(s.binomial(r-1,j-1)*kappa[j]*mu[r-j] for j in range(1,r))))
E=(1/h+x)*(kappa[1]-1)*u+((1+x*h)*kappa[2]-1)*u*u/2
for r in range(3,R+3):E+=(1+x*h)*h**(r-2)*kappa[r]*u**r/s.factorial(r)
E=s.expand(E);es=[E.coeff(h,j) for j in range(R+1)];A=[s.Integer(1)]
for j in range(1,R+1):A.append(s.expand(sum(i*es[i]*A[j-i] for i in range(1,j+1))/j))
ans={}
for j in range(1,R+1):
 v=0
 for (d,),c in s.Poly(A[j],u).terms():
  if d:v-=c*s.hermite_prob(d-1,-x)
 ans[j]=str(s.factor(v))
print(ans)
open((Path(__file__).resolve().parent.parent/'checks'/'central-polynomials.json'),'w').write(json.dumps(ans,indent=2))
