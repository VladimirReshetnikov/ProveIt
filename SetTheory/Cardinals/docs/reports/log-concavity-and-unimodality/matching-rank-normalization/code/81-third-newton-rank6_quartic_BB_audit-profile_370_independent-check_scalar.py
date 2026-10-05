"""Fresh support counts and fraction-free polynomial matrix identity for profile 370."""
from itertools import permutations
from functools import lru_cache
from pathlib import Path
from sympy.polys.matrices import DomainMatrix
import sympy as s,json,time
ROOT=Path(__file__).resolve().parent
@lru_cache(None)
def cnt(cols):return len({tuple(sorted(rows)) for rows in permutations(range(3),len(cols)) if all(c>>i&1 for c,i in zip(cols,rows))})
n,b,p,q,h,k,z=s.symbols('n b p q h k z');E=p+3*n+2*b+3;x=q+2*h+k+3*z;vrs=(q,h,k,z)
r=s.Matrix([p*S.bit_count()+n*cnt((7,S))+b*cnt((3,S))+1 for S in range(1,8)])
G=lambda S:int(bool(S&1))+int(bool(S&2))-int((S&5)==5)-int((S&6)==6)
v=s.Matrix([q*S.bit_count()+h*cnt((3,S))+k*G(S)+z for S in range(1,8)])
B=s.Matrix(7,7,lambda i,j:p*cnt((i+1,j+1))+n*cnt((7,i+1,j+1))+b*cnt((3,i+1,j+1)))
A=3*r*r.T-4*E*B;U=(3*x*r-4*E*v).jacobian(vrs);start=time.time()
da=DomainMatrix.from_Matrix(A).to_dense();adj,den=da.inv_den();du=DomainMatrix.from_Matrix(U).convert_to(da.domain).to_dense();quad=(du.transpose()*adj*du).to_Matrix();de=da.domain.to_sympy(den)
print('fraction-free inverse and contraction',time.time()-start,flush=True)
m,u,g=s.symbols('m u g');reference=s.sympify((ROOT.parent/'profile_370'/'schur.txt').read_text());claimed,cd=s.fraction(reference);claimed=s.expand(claimed.subs({m:n+b,u:n,g:k}));cd=s.expand(cd.subs({m:n+b,u:n,g:k}));P=s.Poly(claimed,*vrs)
checks=0
for i in range(4):
 for j in range(i,4):
  fac=1 if i==j else 2;mon=[0]*4;mon[i]+=1;mon[j]+=1
  lhs=fac*(3*s.diff(x,vrs[i])*s.diff(x,vrs[j])*de-quad[i,j])*cd;rhs=4*E*de*P.coeff_monomial(tuple(mon))
  if not s.Poly(lhs-rhs,n,b,p).is_zero:raise RuntimeError(('scalar coefficient identity',i,j))
  checks+=1
out={'all_pass':True,'matrix_dimension':7,'quadratic_coefficient_identities':checks,'method':'fresh assignment counts and fraction-free inverse, no cached matrix','seconds':time.time()-start};(ROOT/'check_scalar.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
