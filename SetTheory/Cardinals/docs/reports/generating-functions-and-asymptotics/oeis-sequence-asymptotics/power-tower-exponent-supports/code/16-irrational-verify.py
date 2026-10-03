"""Exact parameter-degree and conjugate-elimination checks; requires SymPy."""
import sympy as s,json
from pathlib import Path
a,N,k=s.symbols('a N k');RMAX=6
A=[s.expand(sum(s.prod(a-i for i in range(j))/s.factorial(j)*s.Rational((-1)**(n-j),n-j+1) for j in range(n+1))) for n in range(RMAX+1)]
B=[s.prod(a-i for i in range(1,n+1))/s.factorial(n+1) for n in range(RMAX+1)]
def logcoef(A):
 out=[s.Integer(0)]
 for n in range(1,len(A)):out.append(s.expand(A[n]-sum((j*out[j]*A[n-j] for j in range(1,n)),s.Integer(0))/n))
 return out
la,lb=logcoef(A),logcoef(B);records=[];saved={}
for r in range(1,RMAX+1):
 c=[s.expand((N-r-k)*la[j]+k*lb[j]) for j in range(RMAX+1)]
 v=[s.Integer(1)]
 for n in range(1,r+1):v.append(s.expand(sum(j*c[j]*v[n-j] for j in range(1,n+1))/n))
 R=s.Poly(v[r],N,k);saved[r]=R.as_expr()
 top=sum(coef*N**i*k**j for (i,j),coef in R.terms() if i+j==r)
 expected=((a-s.Rational(1,2))*N-a*k/2)**r/s.factorial(r)
 if s.expand(top-expected)!=0:raise RuntimeError(('top homogeneous',r))
 if s.degree(R.as_expr(),a)>r:raise RuntimeError(('parameter degree',r))
 if s.expand(R.as_expr().subs({N:r,k:0}))!=0:raise RuntimeError(('structural',r))
 if r%2:
  K=a*k-(2*a-1)*N+2*a*r-1
  G=s.cancel(R.as_expr()/K)
  if s.Poly(G,N,k).total_degree()!=r-1:raise RuntimeError(('odd total degree',r))
  if s.degree(G,a)>r-1:raise RuntimeError(('odd parameter degree',r))
  topodd=sum(coef*N**i*k**j for (i,j),coef in s.Poly(G,N,k).terms() if i+j==r-1)
  if s.expand(topodd+((a-s.Rational(1,2))*N-a*k/2)**(r-1)/(2*s.factorial(r)))!=0:raise RuntimeError(('odd top',r))
 records.append({'r':r,'total_degree':R.total_degree(),'parameter_degree':s.degree(R.as_expr(),a),'top_form_pass':True,'structural_point_pass':True})
u=s.symbols('u')
if s.expand(saved[2].subs({N:u+2,k:0})-u*(12*u*a*a-12*(u+1)*a+3*u+5)/24)!=0:raise RuntimeError('nonuniform cutoff family')
minimal=3*a*a-6*a+2
reduced=s.rem(saved[2],minimal,a)
coeffs=[s.Poly(reduced,a).nth(i) for i in range(2)]
G=s.groebner(coeffs,k,N,domain=s.QQ)
expectedN=(N-2)*(N-3)*(9*N*N-N-2)
expectedk=k+s.Rational(3,4)*N**3-s.Rational(37,12)*N*N+s.Rational(7,6)*N+4
if G.reduce(expectedN)[1]!=0 or G.reduce(expectedk)[1]!=0:raise RuntimeError('claimed elimination')
H=s.groebner([expectedN,expectedk],k,N,domain=s.QQ)
if any(H.reduce(g.as_expr())[1]!=0 for g in G.polys):raise RuntimeError('reverse ideal equality')
integerN=[root for root in s.polys.polytools.ground_roots(expectedN,N) if root.is_Integer]
solutions=[]
for n in integerN:
 kval=s.solve(expectedk.subs(N,n),k)[0]
 if not kval.is_Integer:continue
 if any(s.simplify(f.subs({N:n,k:kval}))!=0 for f in coeffs):raise RuntimeError('solution')
 solutions.append({'N':int(n),'k':int(kval),'physical':bool(n>=3 and kval>=0 and kval<=n-2)})
out={'polynomial_checks':records,'minimal_polynomial':str(minimal),'remainder_coefficients':[str(f) for f in coeffs],'groebner_basis':[str(g.as_expr()) for g in G.polys],'integer_solutions':solutions,'all_checks_pass':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
print(json.dumps(out,indent=2,default=str))
