import sympy as s,json
z,L,alpha=s.symbols('z L alpha', nonzero=True)
ell=s.symbols('ell1:5');u=[]
for j in range(1,5):
 d=sum(u[m-1]*z**m for m in range(1,j))
 expr=-alpha*s.log(1+z*d)+sum(ell[r-1]*z**r*(1+z*d)**(-r) for r in range(1,j+1))
 u.append(s.factor(-s.series(expr,z,0,j+1).removeO().coeff(z,j)/L))
d=sum(u[j-1]*z**j for j in range(1,5))
expr=L*d-alpha*s.log(1+z*d)+sum(ell[r-1]*z**r*(1+z*d)**(-r) for r in range(1,5))
res=s.series(expr,z,0,5).removeO().expand();assert s.simplify(res)==0
print(u)
json.dump(dict(coefficients=[str(v) for v in u],residual_through_degree4=str(s.simplify(res))),open('inverse-checks.json','w'),indent=2)
