import sympy as s,time,json,hashlib
from itertools import permutations,combinations
from pathlib import Path
p,m,u,q,h,g,z=s.symbols('p m u q h g z')
def match(cols,slots):return any(all(mask&(1<<j) for mask,j in zip(cols,P)) for P in permutations(slots))
def hp(S,T):return sum(match((S,T),I) for I in combinations(range(3),2))
def cp(S,T,U):return int(match((S,T,U),(0,1,2)))
def gg(S):return int(bool(S&1))+int(bool(S&2))-int(S&5==5)-int(S&6==6)
E=p+2*m+u+3;x=q+2*h+g+3*z
r=s.Matrix([p*S.bit_count()+u*hp(7,S)+(m-u)*hp(3,S)+1 for S in range(1,8)])
v=s.Matrix([q*S.bit_count()+h*hp(3,S)+g*gg(S)+z for S in range(1,8)])
M=3*r*r.T/(4*E)-s.Matrix(7,7,lambda i,j:p*hp(i+1,j+1)+u*cp(7,i+1,j+1)+(m-u)*cp(3,i+1,j+1))
w=3*x*r/(4*E)-v
classes=((1,2),(3,),(4,),(5,6),(7,))
C=s.Matrix(7,5,lambda i,j:int(int(i+1) in classes[j]))
T=C.T*M*C;W=C.T*w
start=time.time(); Y=(C*T.inv()*W).applyfunc(s.cancel);print('inverse seconds',time.time()-start,flush=True)
for i,a in enumerate(M*Y-w):
 if s.cancel(a)!=0:raise Exception(('range',i))
print('range verified',flush=True)
S=s.factor(3*x*x/(4*E)-(w.T*Y)[0]);print('S length',len(str(S)),flush=True)
HERE=Path(__file__).resolve().parent
reference=s.sympify((HERE/'schur.txt').read_text())
if s.cancel(S-reference)!=0:raise ArithmeticError('stored scalar mismatch')
cross=s.Matrix([s.sympify(t) for t in __import__('json').loads((HERE/'cross.json').read_text())])
for value in Y-cross:
 if s.cancel(value)!=0:raise ArithmeticError('stored cross-column mismatch')
print('Both stored exact identities verified',flush=True)
num,den=s.fraction(S)
U,B,P=s.symbols('U B P')
coefficient=s.Poly(num,q).coeff_monomial(q*q)
concavity=s.Poly(s.expand((-coefficient).subs(m,u+B).subs({u:U+1,p:P+1})),U,B,P)
if any(c<0 for c in concavity.coeffs()):raise ArithmeticError('q concavity coefficient')
cones=[]
for du,db in ((2,0),(1,1)):
 poly=s.Poly(s.expand((den/p).subs(m,u+B+db).subs({u:U+du,p:P+1})),U,B,P)
 if any(c<0 for c in poly.coeffs()) or poly.coeff_monomial(1)<=0:
  raise ArithmeticError('denominator positivity')
 cones.append({'u_shift':du,'m_minus_u_shift':db,'terms':len(poly.terms()),
               'constant':int(poly.coeff_monomial(1))})
record={'status':'pass','matrix_identity_verified':True,'scalar_identity_verified':True,
        'q_concavity_terms':len(concavity.terms()),'denominator_cones':cones,
        'scalar_sha256':hashlib.sha256((HERE/'schur.txt').read_bytes()).hexdigest(),
        'cross_sha256':hashlib.sha256((HERE/'cross.json').read_bytes()).hexdigest(),
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'scalar_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
