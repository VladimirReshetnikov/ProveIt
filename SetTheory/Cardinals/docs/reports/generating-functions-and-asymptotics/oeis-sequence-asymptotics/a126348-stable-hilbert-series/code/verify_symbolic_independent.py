import sympy as s
from pathlib import Path
x,L,c,eps,X=s.symbols('t L c epsilon X')
M=6
q=s.exp(-x); delta=1-q
u=s.series(-s.log(delta/x),x,0,M+2).removeO()
G=0
for j in range(1,M+2):
 G+=s.series((-1)**(j+1)*delta**(j-1)/(j*sum(q**k for k in range(j))),x,0,M+1).removeO()
core=s.series(((L+u)**2/2+c)/x-(L+u)/2+x/12-G,x,0,M+1).removeO().expand()
P={j:s.factor(core.coeff(x,j)) for j in range(M+1)}
expected={0:-1,1:(5-L)/24,2:-s.Rational(1,9),3:(2*L+245)/5760,4:-s.Rational(11,900),5:-(8*L+2037)/1451520,6:s.Rational(341,52920)}
for j in expected:
 if s.simplify(P[j]-expected[j])!=0:raise RuntimeError(('modular log coefficient',j,P[j]))
V=s.symbols('V',positive=True); vk={k:s.symbols('v'+str(k)) for k in range(3,9)}
w=-s.I*eps*X/s.sqrt(V)
phase=sum(s.I**k*eps**(k-2)*vk[k]*X**k/(s.factorial(k)*V**s.Rational(k,2)) for k in range(3,9))
amp=sum(eps**(2*j)*(1+w)**j*P[j].subs(L,L-s.log(1+w)) for j in range(1,4))
exponent=s.series(phase+amp,eps,0,7).removeO().expand()
h=[s.expand(exponent.coeff(eps,j)) for j in range(7)]
b=[s.Integer(1)]
for n in range(1,7):b.append(s.expand(sum(k*h[k]*b[n-k] for k in range(1,n+1))/n))
def gaussian(p):
 p=s.Poly(p,X)
 return s.expand(sum(co*s.factorial2(j-1) for (j,),co in p.terms() if j%2==0))
C={j:s.collect(gaussian(b[2*j]),L) for j in range(1,4)}
E1=vk[4]/(8*V**2)-5*vk[3]**2/(24*V**3)
E2=-vk[6]/(48*V**3)+7*vk[3]*vk[5]/(48*V**4)+35*vk[4]**2/(384*V**4)-35*vk[3]**2*vk[4]/(64*V**5)+385*vk[3]**4/(1152*V**6)
want1=P[1]+E1
want2=P[2]+P[1]**2/2+P[1]*E1+E2-1/(48*V)-(6-L)*vk[3]/(48*V**2)
if s.simplify(C[1]-want1)!=0:raise RuntimeError('C1 Gaussian extraction')
if s.simplify(C[2]-want2)!=0:raise RuntimeError('C2 Gaussian extraction')
for j in [1,3,5]:
 if gaussian(b[j])!=0:raise RuntimeError('odd coefficient')
print('PASS: independent modular log coefficients P0..P6; Gaussian C1,C2; odd cancellation')
print('C3 =',C[3])
Path('gaussian_coefficients.txt').write_text('\n'.join('C'+str(j)+' = '+str(C[j]) for j in C)+'\n')
Path('independent_symbolic_results.txt').write_text('P='+str(P)+'\nPASS C1 C2 and odd cancellation\n')
