"""Exact general-a residual and quartic certificates; requires SymPy."""
import sympy as s,json
from pathlib import Path
a,N,k,K,z=s.symbols('a N k K z')
RMAX=6
def log_coeff(A):
 out=[s.Integer(0)]
 for n in range(1,len(A)):
  out.append(s.expand(A[n]-sum(j*out[j]*A[n-j] for j in range(1,n))/n))
 return out
A=[s.expand(sum(s.prod(a-i for i in range(j))/s.factorial(j)*s.Rational((-1)**(n-j),n-j+1) for j in range(n+1))) for n in range(RMAX+1)]
B=[s.prod(a-i for i in range(1,n+1))/s.factorial(n+1) for n in range(RMAX+1)]
la,lb=log_coeff(A),log_coeff(B)
records=[]
c=(a-1)*(2*a+1)
for r in range(RMAX+1):
 coeff=[s.expand((N-r-k)*la[j]+k*lb[j]) for j in range(RMAX+1)]
 v=[s.Integer(1)]
 for n in range(1,r+1):v.append(s.expand(sum(j*coeff[j]*v[n-j] for j in range(1,n+1))/n))
 R=s.factor(v[r]);new=s.cancel(R.subs(k,(K+(2*a-1)*N-2*a*r+1)/a))
 if r%2 and s.cancel(new.subs(K,0))!=0:raise RuntimeError(('reflection',r))
 reduced=s.cancel(new/K) if r%2 else new
 m=r//2
 edge=s.Add(*[coef*N**i*K**j for (i,j),coef in s.Poly(reduced,N,K).terms() if 2*i+j==2*m])
 if any(2*i+j>2*m for (i,j),coef in s.Poly(reduced,N,K).terms()):raise RuntimeError(('weight',r))
 alpha=s.Rational(1,2) if r%2 else -s.Rational(1,2)
 fac=-s.factorial(m)/(2*s.factorial(r)) if r%2 else s.factorial(m)/s.factorial(r)
 pred=fac*(c*N/6)**m*s.assoc_laguerre(m,alpha,-3*K*K/(2*c*N))
 if s.cancel(edge-pred)!=0:raise RuntimeError(('edge',r))
 if r in [4,5]:
  U=a*K+c*N-2*a*a*r+a-1
  oldk=(K+(2*a-1)*N-2*a*r+1)/a
  V=N+1-a**4*oldk
  predicted=(15*K**4+30*K*K*U+5*U*U+2*V)/5760 if r==4 else -K*(3*K**4+10*K*K*U+5*U*U+2*V)/11520
  if s.cancel(new-predicted)!=0:raise RuntimeError(('small residual',r))
 records.append({'r':r,'reflection_and_edge_pass':True})
 print('residual',r,'passed',flush=True)
b=-(2*a**3+a*a+a+1)/(2*a+1);e=a*(a+1)/(2*a+1)
quartics=[]
for r,prime,constant in [(4,3,27000000),(5,11,8000)]:
 f=-2*a*(a+1)*((r+1)*a-1)/(2*a+1)
 C=-2*a*a*r+a-1;D=2*a**4*r-a**3+1
 if s.cancel(D-b*C-f)!=0:raise RuntimeError(('f',r))
 Q=s.cancel(((150 if r==4 else 10)*K**4+(30 if r==4 else 10)*b*K*K-10*e*K+b*b-10*f)*(2*a+1)**2)
 delta=s.discriminant(Q,K)
 DD=s.Poly(s.cancel(delta/(constant*(2*a+1)**6)),a)
 if DD.degree()!=18 or any(not x.is_Integer for x in DD.all_coeffs()):raise RuntimeError(('discriminant factor',r))
 vals=[int(DD.eval(j))%prime for j in range(prime)]
 if 0 in vals or int(DD.LC())%prime==0:raise RuntimeError(('no rational root',r))
 quartics.append({'r':r,'quartic_times_denominator':str(Q),'discriminant_constant':constant,
 'D_coefficients_descending':[int(x) for x in DD.all_coeffs()],
 'prime':prime,'D_values_mod_prime':vals,'leading_coefficient_mod_prime':int(DD.LC())%prime})
 print('quartic',r,'passed',flush=True)
Path(__file__).with_name('certificates.json').write_text(json.dumps({'residual_checks':records,'quartic_certificates':quartics,'all_checks_pass':True},indent=2)+'\n')
