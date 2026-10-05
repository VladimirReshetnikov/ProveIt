import sympy as s
from pathlib import Path
x,L=s.symbols('t L'); c=s.symbols('c')
M=7
def tr(e, n=M+1): return s.series(e,x,0,n).removeO().expand()
delta=tr(1-s.exp(-x), M+3)
lam=L-tr(s.log(delta/x),M+3)
li2=tr(sum((-delta)**j/s.Integer(j*j) for j in range(1,M+3)),M+3)
expr=tr((lam**2/2+c+li2)/x-lam/2-s.log(1+delta)/2)
z=s.symbols('z'); li=z/(1-z)
for m in range(1,(M+2)//2+1):
 if m>1:
  li=s.factor(z*s.diff(z*s.diff(li,z),z))
 expr=tr(expr-s.bernoulli(2*m)*x**(2*m-1)/s.factorial(2*m)*li.subs(z,-1/delta))
P={j:s.factor(expr.coeff(x,j)) for j in range(-1,M+1)}
print('LOG PRODUCT')
for j,p in P.items(): print(j,p)
V={0:L**2/2+c}
for j in range(1,9): V[j]=s.expand(j*V[j-1]+s.diff(V[j-1],L))
E1=V[4]/(8*V[2]**2)-5*V[3]**2/(24*V[2]**3)
E2=-V[6]/(48*V[2]**3)+7*V[3]*V[5]/(48*V[2]**4)+35*V[4]**2/(384*V[2]**4)-35*V[3]**2*V[4]/(64*V[2]**5)+385*V[3]**4/(1152*V[2]**6)
C1=s.factor(P[1]+E1)
C2=P[2]+P[1]**2/2+P[1]*E1+E2-1/(48*V[2])-(6-L)*V[3]/(48*V[2]**2)
print('V',V)
print('C1',C1)
print('C2',s.factor(C2))
Path('symbolic_results.txt').write_text('P='+str(P)+'\nV='+str(V)+'\nC1='+str(C1)+'\nC2='+str(s.factor(C2))+'\n')
