from pathlib import Path
import sympy as s,json
h,u,v=s.symbols('h u v');R=7;D=(R+2)//2
tr=lambda a:s.Add(*(c*v**i[0] for i,c in s.Poly(s.expand(a),v).terms() if i[0]<=D))
mu=[s.Integer(1)]
for r in range(1,R+3):
 p=s.factorial(r)
 for j in range(1,r+1):p=tr(p*sum((-j*v)**l for l in range(D+1)))
 mu.append(p)
kap=[s.Integer(0)]
for r in range(1,R+3):kap.append(tr(mu[r]-sum(s.binomial(r-1,j-1)*kap[j]*mu[r-j] for j in range(1,r))))
kap=[x.subs(v,h*h) for x in kap]
E=(kap[1]-1)/h*u+(kap[2]-1)*u*u/2
for r in range(3,R+3):E+=h**(r-2)*kap[r]*u**r/s.factorial(r)
E=s.expand(E);es=[E.coeff(h,j) for j in range(R+1)];A=[s.Integer(1)]
for j in range(1,R+1):A.append(s.expand(sum(i*es[i]*A[j-i] for i in range(1,j+1))/j))
ans={}
for j in range(1,R+1):
 ans[j]=str(s.simplify(-sum(c*s.hermite_prob(d[0]-1,0) for d,c in s.Poly(A[j],u).terms() if d[0])))
print(ans)
open((Path(__file__).resolve().parent.parent/'checks'/'diagonal-coefficients.json'),'w').write(json.dumps(ans,indent=2))
