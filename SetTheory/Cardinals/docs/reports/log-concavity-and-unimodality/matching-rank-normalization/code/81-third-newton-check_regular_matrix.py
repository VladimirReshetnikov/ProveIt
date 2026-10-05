from itertools import combinations
from fractions import Fraction
A=[[0,0,0,1,1,1],[1,1,1,0,0,1],[-1,0,1,-1,0,-1],[0,1,2,0,1,1]]
n=6;d=[sum(r[i]!=0 for r in A) for i in range(n)];p=[[0]*n for _ in range(n)]
for i,j in combinations(range(n),2):p[i][j]=p[j][i]=sum(A[a][i]*A[b][j]!=A[a][j]*A[b][i] for a,b in combinations(range(4),2))
G=[[2*d[i]*d[j]-3*p[i][j] for j in range(n)] for i in range(n)]
z=[3,3,1,4,4,-2];q=sum(z[i]*G[i][j]*z[j] for i in range(n) for j in range(n));M=[[Fraction(x) for x in r] for r in G];det=Fraction(1)
for i in range(n):
 j=next(j for j in range(i,n) if M[j][i])
 if j!=i:M[i],M[j]=M[j],M[i];det=-det
 v=M[i][i];det*=v
 for j in range(i+1,n):
  t=M[j][i]/v
  for k in range(i,n):M[j][k]-=t*M[i][k]
if not (A[3]==[sum(A[i][j] for i in range(3)) for j in range(n)]): raise ArithmeticError("Exact counterexample check failed")
if not ([[A[i][j] for j in [0,1,3]] for i in range(3)]==[[0,0,1],[1,1,0],[-1,0,-1]]): raise ArithmeticError("Exact counterexample check failed")
if not (d==[2,2,3,2,2,4] and q==-4 and det==-62208): raise ArithmeticError("Exact counterexample check failed")
print('PASS rank3 unit4x6 regular-minor obstruction; det3Q=',det,'quadratic=',q)
print('3Q=',G)
