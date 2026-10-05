"""Exact canonical endpoint and ratio conversion for tree-child formal profiles."""
import sympy as S,json,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
from derive_tree import D,x,k,t
M=int(sys.argv[1]) if len(sys.argv)>1 else 9
a=S.symbols('a');J=M-3
inp=json.load(open(BASE/f'formal_{M}.json'))
fs=[[S.sympify(v) for v in p] for p in inp['f']];sig=[S.sympify(v) for v in inp['sigma']]
logs=S.series(S.log(sum(sig[j]*t**j for j in range(len(sig)))/2),t,0,M+1).removeO().expand()
ell=[]
hdiff=S.Rational(3,2)*k/t*(1-(1-t**3)**S.Rational(1,3))-sig[3]/2*S.log(1-t**3)
for j in range(1,J+1):
 rhs=S.series(hdiff,t,0,j+4).removeO().expand().coeff(t,j+3)
 ee=S.factor((rhs-logs.coeff(t,j+3))*3/j)
 ell.append(ee)
 hdiff+=ee*t**j*(1-(1-t**3)**(-S.Rational(j,3)))
endpoint=0
for j,fp in enumerate(fs):
 for p in range(0,J+2-j):
  endpoint+=fp[1].subs(x,0)*t**(j+p-1)/S.factorial(p)
  fp=D(fp)
E=S.series(endpoint,t,0,J+1).removeO()
le=S.series(S.log(E)-S.log(1+S.Rational(2,3)*t**3),t,0,J+1).removeO().expand()
ell_diag=[S.simplify((ell[j-1]+le.coeff(t,j)).subs(k,S.Rational(2,3)**S.Rational(2,3)*a)*2**(-S.Rational(j,3))) for j in range(1,J+1)]
print('ell=',ell)
print('E=',S.factor(E))
print('log correction coeffs',ell_diag)
delta=S.series(S.exp(sum(ell_diag[j-1]*t**j for j in range(1,J+1))),t,0,J+1).removeO().expand()
deltas=[S.simplify(delta.coeff(t,j)) for j in range(J+1)]
print('multiplicative coeffs',deltas)
# ratio a_n/(12n a_(n-1)), t now n^(-1/3)
qr=3**S.Rational(1,3)*a/t*(1-(1-t**3)**S.Rational(1,3))+S.Rational(2,3)*S.log(1-t**3)
for j,ee in enumerate(ell_diag,1):qr+=ee*t**j*(1-(1-t**3)**(-S.Rational(j,3)))
qr=S.series(qr,t,0,M+1).removeO()
qser=S.series(S.exp(qr),t,0,M+1).removeO().expand()
qcoeff=[S.simplify(qser.coeff(t,j)) for j in range(M+1)]
print('ratio a_n/(12n a_(n-1)) coeffs',qcoeff)
res={'ell':[str(z) for z in ell],'E':str(E),'log_correction':[str(z) for z in ell_diag],'multiplicative':[str(z) for z in deltas],'ratio':[str(z) for z in qcoeff]}
json.dump(res,open(BASE/f'endpoint_{M}.json','w'),indent=2)
