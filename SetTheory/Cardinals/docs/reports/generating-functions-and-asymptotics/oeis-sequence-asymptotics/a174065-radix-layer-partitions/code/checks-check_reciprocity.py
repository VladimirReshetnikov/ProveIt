import mpmath as m,json,pathlib
from check_radix import constants,coeff
m.mp.dps=90

def positive_logf(b,t):
 total=m.mpf(0)
 while t<230:
  for k in range(1,int(m.ceil(230/t))+1):total+=m.log1p(m.exp(-k*t))
  t*=b
 return total
out=[]
for b,t in [(2,1),(3,2),(4,1),(4,3),(8,2),(8,5),(16,8)]:
 t=m.mpf(t);A,beta,C,d=constants(b);u=-m.log(t)/m.log(b)
 P=2*m.re(sum(coeff(b,k)*m.exp(2j*m.pi*k*u) for k in range(1,100)))
 lhs=positive_logf(b,t);main=A/t+beta*m.log(t)+C+P-d*t;dual=positive_logf(b,2*m.pi*m.pi*b/t)
 out.append({'b':b,'t':str(t),'radial_remainder':str(lhs-main),'dual_log_product':str(dual),'identity_error':str(lhs-main-dual)})
pathlib.Path(__file__).with_name('reciprocity-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
