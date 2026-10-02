import mpmath as m, sympy as s, pathlib,json,math
from check_radix import constants,coeff
m.mp.dps=65
p=pathlib.Path(__file__).parent
z=s.Symbol('z');out={}
for b in [4,8]:
 mx=10000;power=int(round(math.log2(b)))
 v=[0]*(mx+1);v[0]=1
 for k in range(1,mx+1):
  if ((k&-k).bit_length()-1)%power==0:
   for n in range(k,mx+1):v[n]+=v[n-k]
 A,beta,C,d=constants(b);K=m.exp(C)*A**(beta/2+m.mpf(1)/4)/(2*m.sqrt(m.pi));kap=beta/2+m.mpf(3)/4
 fourier=[(2j*m.pi*k/m.log(b),coeff(b,k)) for k in range(1,35)]
 betaexact=s.Rational(1,2*power);rpolys=[]
 for j in range(5):
  expr=(-1)**j*s.prod(4*(betaexact+1-z)**2-(2*l-1)**2 for l in range(1,j+1))/(s.factorial(j)*16**j)
  rpolys.append(s.Poly(expr,z))
 rows=[]
 for n in [100,400,1000,2500,5000,10000]:
  N=n-d;u=m.log(m.sqrt(N/A))/m.log(b)
  pd=[2*m.re(sum(c*sk**j*m.exp(sk*m.log(b)*u) for sk,c in fourier)) for j in range(9)]
  h=[m.mpf(1)]
  for j in range(1,9):h.append(sum(math.comb(j-1,k-1)*pd[k]*h[j-k] for k in range(1,j+1)))
  r=[]
  for poly in rpolys:r.append(sum(m.mpf(str(cc.p))/int(cc.q)*h[mon[0]] for mon,cc in poly.terms()))
  main=K*N**(-kap)*m.exp(2*m.sqrt(A*N)+pd[0]);ap=[]
  for J in range(5):
   approx=main*sum(r[j]*(A*N)**(-m.mpf(j)/2) for j in range(J+1));ap.append(str(approx/v[n]-1))
  rows.append({'n':n,'phase':str(u%1),'exact':str(v[n]),'envelope_ratio':str(m.mpf(v[n])/(K*n**(-kap)*m.exp(2*m.sqrt(A*n)))),'H':str(m.exp(pd[0])),'relative_errors_orders_0_to_4':ap})
 out[str(b)]={'first_32':v[:32],'checks':rows}
(p/'coefficient-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
