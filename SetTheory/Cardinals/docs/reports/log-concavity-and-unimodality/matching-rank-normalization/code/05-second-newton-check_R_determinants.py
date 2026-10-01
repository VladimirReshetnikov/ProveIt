from itertools import combinations,permutations
import sympy as s
n=s.symbols('n')
def pair(U,V):
 return sum(any((U>>a&1) and (V>>b&1) for a,b in permutations(S)) for S in combinations(range(3),2))
def triple(U,V,W):
 return int(any(all(mask>>i&1 for mask,i in zip((U,V,W),p)) for p in permutations(range(3))))
expected={1:6250*n**4*(n+1)**8,3:15625*n**4*(n+2)**7*(2*n*n+4*n+3),7:31250*n**3*(n+2)**2*(n+3)**6*(2*n*n+7*n+9)}
for J in (1,3,7):
 S=list(range(1,7 if J==1 else 8));E=n+J.bit_count();r={U:n*U.bit_count()+pair(J,U) for U in S}
 A=s.Matrix([[s.expand(4*r[U]*r[V]-5*E*(n*pair(U,V)+triple(J,U,V))) for V in S] for U in S])
 d=s.factor(A.det(method='domain-ge'))
 if s.expand(d-expected[J])!=0:raise RuntimeError(('R determinant mismatch',J))
 print('PASS',J,d,flush=True)
