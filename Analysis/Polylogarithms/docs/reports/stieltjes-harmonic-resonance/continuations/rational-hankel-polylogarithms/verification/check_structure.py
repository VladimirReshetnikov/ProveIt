from pathlib import Path
from itertools import combinations,product
import json,time
import sympy as S
from compiler import *
if not __debug__:raise RuntimeError('Do not use -O for verification.')
root=Path(__file__).resolve().parents[1]
counts={'capacity_tests':0,'sharp_coefficients':0,'top_compressions':0,'endpoint_coefficients':0,'confluent_factorizations':0,'negative_controls':0}
records=[]

def wdegree(ex):
 hs=sorted([h for h in ex.free_symbols if h.name.startswith('H') and h.name[1:].isdigit()],key=str)
 if not hs:return 0
 return max(sum(int(h.name[1:])*a for h,a in zip(hs,es)) for es,c in S.Poly(ex,*hs).terms() if c!=0)

def norm_product(q):
 return S.prod(S.prod(M-j+t for t in range(2*j+1))/((2*j+1)*S.binomial(2*j,j)**2) for j in range(q))

for ss in range(1,8):
 for r in range(1,5):
  ex=hankel(r,[(0,ss,1)])
  W=capacity(r,[(0,ss,1)]); assert wdegree(ex)==W
  kk=min(r,(ss+1)//2);q=r-kk
  hs=sorted([h for h in ex.free_symbols if h.name.startswith('H')],key=str)
  target=harmonic_symbol(ss-kk+1)**kk
  got=S.Poly(ex,*hs).coeff_monomial(target)
  expect=S.Integer(-1)**(kk*(kk-1)//2)*norm_product(q)
  if q and ss%2:expect*=S.rf(M+1,q)/S.binomial(2*q,q)
  assert S.cancel(got-expect)==0,(ss,r,got,expect)
  counts['capacity_tests']+=1;counts['sharp_coefficients']+=1
  records.append({'pole_order':ss,'rank':r,'formal_weight':W,'sharp_monomial':str(target),'coefficient':str(S.factor(expect))})

# Several poles, computed separately using a monic change-of-basis compression.
for shifts in [(0,1),(0,2),(0,1,2),(0,2,4)]:
 d=len(shifts)
 for q in [0,1]:
  r=d+q;cs=[S.Integer(j+1) for j in range(d)]
  poles=[(a,1,c) for a,c in zip(shifts,cs)]
  X=harmonic_symbol(1)
  ex=hankel(r,poles)
  got=S.Poly(ex,X).coeff_monomial(X**d)
  x=S.symbols('x');L=S.prod(x+a for a in shifts)
  W=S.expand(sum(c*L*(S.div(L,x+a,x)[0]) for a,c in zip(shifts,cs)))
  vals=[sum(c*power_sum(int(p[0])+j) for p,c in S.Poly(W,x).terms()) for j in range(2*q-1)] if q else []
  gram=S.Matrix(q,q,lambda i,j:vals[i+j]).det() if q else S.Integer(1)
  pref=S.prod(cs)*S.prod((b-a)**2 for a,b in combinations(shifts,2))
  assert S.cancel(got-pref*gram)==0,(shifts,q)
  counts['top_compressions']+=1

# Independent local jet decomposition at actual integer cutoffs.
x=S.symbols('x')
for poles in [[(0,3,2)],[(1,4,3)],[(0,2,1),(2,3,-2)],[(0,1,1),(1,1,2),(4,1,3)]]:
 orders={a:max(e for aa,e,c in poles if aa==a) for a,e,c in poles}
 R=sum(c/(x+a)**ell for a,ell,c in poles)
 for r in [2,3,4]:
  n=5
  harmonic=S.zeros(r)
  for a,ss in orders.items():
   V=S.Matrix(r,ss,lambda i,p:S.binomial(i,p)*S.Integer(-a)**(i-p) if p<=i else 0)
   C=S.Matrix(ss,ss,lambda p,q:sum(c*sum(S.Rational(1,k+a)**(ell-p-q) for k in range(1,n+1)) for aa,ell,c in poles if aa==a and ell>=p+q+1))
   harmonic+=V*C*V.T
  B=S.zeros(r)
  for i in range(r):
   for j in range(r):
    num,den=S.fraction(S.cancel(x**(i+j)*R))
    Q=S.div(num,den,x)[0]
    B[i,j]=sum(Q.subs(x,k) for k in range(1,n+1))
  direct=S.Matrix(r,r,lambda i,j:sum((x**(i+j)*R).subs(x,k) for k in range(1,n+1)))
  assert S.simplify(B+harmonic-direct)==S.zeros(r)
  counts['confluent_factorizations']+=1

# Endpoint principal parts from the bordered determinant formula.
X=harmonic_symbol(1);t=S.symbols('t')
for r,poles in [(2,[(0,1,1),(1,1,2)]),(2,[(0,1,1),(1,1,2),(2,1,3)]),(3,[(0,1,1),(1,1,1),(2,1,1)])]:
 mat=S.Matrix(r,r,lambda i,j:moment(i+j,poles));de=S.factor(mat.det())
 for h in range(1,max(a for a,ell,c in poles)+1):
  active=[(a,c) for a,ell,c in poles if a>=h]
  C=sum((c*S.Matrix([S.Integer(-a)**i for i in range(r)])*S.Matrix([[S.Integer(-a)**i for i in range(r)]] ) for a,c in active),S.zeros(r))
  A=(mat-C/(M+h)).applyfunc(S.cancel)
  for ell in range(1,min(r,len(active))+1):
   val=0
   for k in range(ell,min(r,len(active))+1):
    for subset in combinations(active,k):
     V=S.Matrix(r,k,lambda i,j:S.Integer(-subset[j][0])**i)
     border=A.row_join(V).col_join(V.T.row_join(S.zeros(k)))
     f=S.cancel(border.det(method='domain-ge'))
     val+=S.Integer(-1)**k*S.prod(c for a,c in subset)*S.diff(f,M,k-ell).subs(M,-h)/S.factorial(k-ell)
   direct=S.expand(S.series(de.subs(M,t-h),t,0,1).removeO()).coeff(t,-ell)
   assert S.simplify(val-direct)==0,(r,h,ell,val,direct)
   counts['endpoint_coefficients']+=1
# Corrupt the sign in the single triple-pole extremal minor.
assert S.Poly(hankel(2,[(0,3,1)]),harmonic_symbol(1),harmonic_symbol(2),harmonic_symbol(3)).coeff_monomial(harmonic_symbol(2)**2)!=1
counts['negative_controls']+=1
(root/'data'/'structural_checks.json').write_text(json.dumps({'counts':counts,'sharp_coefficient_examples':records},indent=2))
print(json.dumps(counts,indent=2))
