import json
from pathlib import Path
import mpmath as m
m.mp.dps=80
g=m.euler
z=lambda n:m.zeta(n)
b=-g;c1=z(2);c2=-z(3)
r=-4*b**3+12*b*c1-4*c2
d=6*b*b-4*c1
# Taylor coefficients of psi^4 after multiplying by x^4.
K=80
p=[-m.mpf(1),-g]+[(-1)**(k+1)*z(k+1) for k in range(1,K+4)]
a=[m.mpf(1)]
for j in range(4):
 a=[sum(a[i]*p[k-i] for i in range(len(a)) if 0<=k-i<len(p)) for k in range(min(K+5,len(a)+len(p)-1))]
cut=m.mpf('0.05')
small=sum(a[k]*cut**(k-3)/(k-3) for k in range(4,len(a)))
def f(x):
 return m.psi(0,x)**4-x**-4+4*b*x**-3-d*x**-2-r/x
Qquad=-m.mpf(1)/3+2*b-d+small+m.quad(f,[cut,m.mpf('.2'),m.mpf('.5'),1])
base=18*z(4)+12*z(3)-12*g*z(2)+4*m.diff(z,3)+12*m.stieltjes(3)-24*z(2)*m.stieltjes(1)
records=[]
for N,K in [(30,20),(50,30),(80,40)]:
 ps=[m.mpf(0)]*(K+1)
 ps[1]=-m.mpf(1)/2
 for k in range(2,K+1,2):ps[k]=-m.bernoulli(k)/k
 tail=0
 for k in range(1,K+1):
  q=sum(ps[i]*ps[k-i] for i in range(1,k))+(1 if k==1 else -(k-1)*ps[k-1])
  tail+=2*ps[k]*m.diff(lambda s:m.zeta(s,N),k+1,2)-q*m.diff(lambda s:m.zeta(s,N),k+1)
 total=sum((m.psi(0,n)**2+m.psi(1,n)-m.log(n)**2)*m.log(n)/n for n in range(1,N))+tail
 value=base+12*total
 print('N,K',N,K)
 print('Q_arithmetic',m.nstr(value,70))
 print('difference',m.nstr(value-Qquad,12))
 records.append({'N':N,'asymptotic_order':K,'value':m.nstr(value,75),'absolute_difference':m.nstr(abs(value-Qquad),15)})
print('Q_quad',m.nstr(Qquad,70))
print('quartic principal',*[m.nstr(x,20) for x in [1,-4*b,d,r]])

report={'precision_dps':m.mp.dps,'mpmath_version':m.__version__,'kind':'non_interval_numerical_diagnostic','quadrature_value':m.nstr(Qquad,75),'quad_local_series_order':80,'quad_split':str(cut),'arithmetic_checks':records}
Path(__file__).with_name('quartic_numeric_results.json').write_text(json.dumps(report,indent=2)+'\n')
assert abs(value-Qquad)<m.mpf('1e-60')
