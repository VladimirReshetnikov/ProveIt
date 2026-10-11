"""Independent Mellin evaluations of the strict harmonic Laurent coefficients."""
import json
from pathlib import Path
import mpmath as m
m.mp.dps=80
g=m.euler
z=lambda k:m.zeta(k)
# expm1 denominators are evaluated by convergent local series near zero.
def local(t):
 v=-t/2+sum(m.bernoulli(2*k)*t**(2*k)/(2*k*m.factorial(2*k)) for k in range(1,34))
 b=-m.mpf(1)/2+sum(m.bernoulli(2*k)*t**(2*k-1)/m.factorial(2*k) for k in range(1,34))
 return v,b
def hs(t,depth):
 L=m.log(t)
 if t<m.mpf('.1'):v,b=local(t)
 else:
  v=m.log(-m.expm1(-t)/t)
  b=1/m.expm1(t)-1/t
 if depth==2:
  return -L*b-v*(1/t+b)
 return (L*L*b+(2*L*v+v*v)*(1/t+b))/2
def gfun(t,depth):
 A=m.log(-m.expm1(-t))
 return (-A if depth==2 else A*A/2)/m.expm1(t)
def J(depth,j):
 return m.quad(lambda t:m.log(t)**j*hs(t,depth),[0,m.mpf('.05'),m.mpf('.1'),1])+m.quad(lambda t:m.log(t)**j*gfun(t,depth),[1,3,10,m.inf])
c3=g**3/6-g*z(2)/2+z(3)/3
c4=g**4/24-g*g*z(2)/4+g*z(3)/3+z(4)/16
J20,J21=J(2,0),J(2,1)
J30,J31=J(3,0),J(3,1)
eta=c3+g*J20+J21
beta=c4+g*J30+J31
Q3=3*z(2)-6*eta-6*g*m.stieltjes(1)
Q4=18*z(4)+12*z(3)-12*g*z(2)+4*m.diff(z,3)+12*(g*g-z(2))*m.stieltjes(1)+24*g*eta-24*beta
quad_results=json.loads(Path(__file__).with_name('quartic_numeric_results.json').read_text())
quad_value=m.mpf(quad_results['quadrature_value'])
results={'precision_dps':m.mp.dps,'mpmath_version':m.__version__,
         'kind':'non_interval_numerical_diagnostic',
         'eta_from_mellin':m.nstr(eta,70),'beta1_from_mellin':m.nstr(beta,70),
         'Q3_from_mellin':m.nstr(Q3,70),'Q4_from_mellin':m.nstr(Q4,70),
         'Q4_quadrature_discrepancy':m.nstr(Q4-quad_value,15),
         'J20':m.nstr(J20,60),'J21':m.nstr(J21,60),'J30':m.nstr(J30,60),'J31':m.nstr(J31,60)}
Path(__file__).with_name('quartic_mellin_results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))

assert abs(Q4-quad_value)<m.mpf('1e-70')
