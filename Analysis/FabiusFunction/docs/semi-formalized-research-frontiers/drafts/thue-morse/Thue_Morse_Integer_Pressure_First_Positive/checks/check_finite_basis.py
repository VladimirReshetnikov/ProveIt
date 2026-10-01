"""Independent finite Bernoulli formula checked against Fourier response data."""
from pathlib import Path
import json
import sympy as s
root=Path(__file__).resolve().parent.parent
c=lambda j:(-1)**(j+1)*2**(2*j)*s.bernoulli(2*j)/s.factorial(2*j)
R=lambda j:(2**(2*j)-1)*c(j)
f=lambda l,u:(4-l*(3-u))/(2*(1-l)*(1-u))
rows=[]
for old in json.loads((root/'data'/'second_response_checks.json').read_text())['rows']:
 m=old['m'];bb=[]
 for j in range(1,m):
  q=4*m*m*sum(c(k)*c(j+1-k)*f(s.Rational(1,4**j),s.Rational(1,2**(2*k-1))) for k in range(1,j+1))
  if j<=m-2:q-=2*m*(2*j+1)*c(j+1)*f(s.Rational(1,4**j),s.Rational(1,2**(2*j+1)))
  assert q>0
  lower=2*m*f(s.Rational(1,4**j),s.Rational(1,2**(2*j+1)))*(2*m*(2*j+3)-(2*j+1))*c(j+1)
  assert q>=lower>0
  assert sum(c(k)*c(j+1-k)for k in range(1,j+1))==(2*j+3)*c(j+1)
  bb.append(q)
 B=sum(bb[j-1]*R(m-j)for j in range(1,m))
 assert B==s.Rational(old['B'])
 rows.append({'m':m,'positive_basis_coefficients':[str(x)for x in bb],'B':str(B),'matches_fourier':True})
(root/'data'/'finite_basis_checks.json').write_text(json.dumps({'rows':rows,'all_checks_passed':True},indent=2)+'\n')
print('Finite Bernoulli formula, coefficient positivity and bounds agree with independent Fourier values for m=2,...,10.')
