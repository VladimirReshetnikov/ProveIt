"""Exact finite coefficient extraction from the repeated-pole counterterm.

The regular digamma germ is truncated beyond every coefficient needed by
the displayed cases. Z2, ..., Z7 are formal zeta symbols. This verifies
finite algebra, not the analytic collision theorem.
"""
import sympy as s
E,X,L=s.symbols('e x L');G=s.symbols('gamma');Z={k:s.symbols('Z'+str(k)) for k in range(2,8)}
def h(r,y):
 return s.diff(G+sum((-1)**k*Z[k+1]*X**k for k in range(1,7)),X,r).subs(X,y)
def f(r,y):return (-1)**r*s.factorial(r)/y**(r+1)+h(r,y)
def calc(rs,cs):
 n=[r+1 for r in rs];kap=[(-1)**r*s.factorial(r) for r in rs];a=[s.Integer(c)*E for c in cs];C=0
 for m in range(len(rs)):
  for i in range(m+1,len(rs)):
   K=kap[m]/(X+a[m])**n[m]
   for k in range(m):K*=h(rs[k],X+a[k])
   for k in range(m+1,len(rs)):
    if k!=i:K*=f(rs[k],X+a[k])
   for p in range(1,n[i]+1):
    B=kap[i]*s.diff(K,X,n[i]-p).subs(X,-a[i])/s.factorial(n[i]-p)
    if p==1:term=-B*(L+s.log(cs[i]-cs[m]))
    else:term=B/(p-1)/(a[i]-a[m])**(p-1)
    C+=s.expand(term).coeff(E,0)
 return s.expand(C)
assert s.simplify(calc([0,1,0],[0,1,2])-Z[3]*(1-s.log(2))) == 0
for rs in [[1,0,0],[0,1,0],[0,0,1],[1,1,0],[0,1,1],[2,0,0]]:
 print(rs,calc(rs,[0,1,2]))
