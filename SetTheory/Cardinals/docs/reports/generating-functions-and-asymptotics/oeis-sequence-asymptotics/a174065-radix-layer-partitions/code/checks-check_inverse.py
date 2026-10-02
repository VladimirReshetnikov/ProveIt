import mpmath as m, sympy as s, pathlib,json,math
from check_radix import constants,coeff
m.mp.dps=60
p=pathlib.Path(__file__).parent;data=json.load(open(p/'coefficient-checks.json'));out={};z=s.Symbol('z')
for b in [4,8]:
 A,beta,C,d=constants(b);K=m.exp(C)*A**(beta/2+m.mpf(1)/4)/(2*m.sqrt(m.pi));kap=beta/2+m.mpf(3)/4
 fs=[(2j*m.pi*k/m.log(b),coeff(b,k)) for k in range(1,25)]
 polys=[s.Poly((-1)**j*s.prod(4*(s.Rational(1,2*int(math.log2(b)))+1-z)**2-(2*l-1)**2 for l in range(1,j+1))/(s.factorial(j)*16**j),z) for j in range(5)]
 def logapprox(n,J,periodic=True):
  N=n-d;u=m.log(m.sqrt(N/A))/m.log(b)
  pd=[2*m.re(sum(c*sk**j*m.exp(sk*m.log(b)*u) for sk,c in fs)) if periodic else m.mpf(0) for j in range(9)]
  h=[m.mpf(1)]
  for j in range(1,9):h.append(sum(math.comb(j-1,k-1)*pd[k]*h[j-k] for k in range(1,j+1)))
  rs=[sum(m.mpf(str(cc.p))/int(cc.q)*h[mon[0]] for mon,cc in poly.terms()) for poly in polys]
  return m.log(K)-kap*m.log(N)+2*m.sqrt(A*N)+pd[0]+m.log(sum(rs[j]*(A*N)**(-m.mpf(j)/2) for j in range(J+1)))
 rows=[]
 for row in data[str(b)]['checks']:
  n=row['n'];Y=m.log(int(row['exact']));errs=[]
  for J in [0,1,2,3,4]:
   x=m.findroot(lambda x:logapprox(x,J)-Y,(m.mpf(n)-1,m.mpf(n)+1));errs.append(str(x-n))
  xp=m.findroot(lambda x:logapprox(x,4,False)-Y,(m.mpf(n)-1,m.mpf(n)+1))
  rows.append({'n':n,'inverse_index_errors_orders_0_to_4':errs,'inverse_error_ignoring_periodic_factor_order4':str(xp-n)})
 out[str(b)]=rows
(p/'inverse-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
