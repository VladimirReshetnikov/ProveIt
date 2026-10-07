import sympy as s, json, math
from fractions import Fraction
from pathlib import Path
out=Path(__file__).parent
lam,t,r,q=s.symbols('lam t r q')
# Original triangle, independently marked only after the n=2 base.
row=[s.Integer(0),s.Integer(1),s.Integer(1)]
polys=[s.Integer(1)]
rows={2:list(map(str,row))}
for n in range(3,19):
    nxt=[s.Integer(0)]*(n+1)
    nxt[1]=lam*row[-1]
    for k in range(2,n+1):
        nxt[k]=s.expand(nxt[k-1]+(n-2)*row[n-k])
    row=nxt;polys.append(row[-1]);rows[n]=list(map(str,row))
# Independent formal ODE coefficients.
M=17
e=[s.Integer(1)]
for n in range(M):
    e.append(s.expand((sum(e[j]*e[n-j] for j in range(n+1))+(1 if n==0 else 0))/(2*(n+1))))
a=[s.Integer(1)]
for n in range(M):
    a.append(s.expand(lam*sum(e[j]*a[n-j] for j in range(n+1))/(n+1)**2))
b=[s.expand(sum(e[j]*a[n-j] for j in range(n+1))) for n in range(M)]
if not all(s.expand(math.factorial(N)**2*b[N]-polys[N])==0 for N in range(M)):
    raise RuntimeError('Marked ODE identity failed')
p=s.Poly(polys[8],lam)
st=s.sturm(p.as_expr(),lam)
def sg(x): return 1 if x>0 else -1
def signs_inf(d):
    return [sg(s.LC(s.Poly(f,lam)))*((-1)**s.degree(f,lam) if d<0 else 1) for f in st]
def var(ls): return sum(x!=y for x,y in zip(ls,ls[1:]))
sm,sp=signs_inf(-1),signs_inf(1)
real=var(sm)-var(sp)
if not (real==6 and p.degree()==8 and s.gcd(p,p.diff()).degree()==0):
    raise RuntimeError('Exact root count or squarefreeness failed')
if not all(x>0 for x in p.all_coeffs()):
    raise RuntimeError('Coefficient positivity failed')
# Local Frobenius recursion, checked directly through t^5 including marking.
C=s.series(r*t*s.cot(r*t/2),t,0,12).removeO().expand()
h=[s.Integer(0),s.Integer(1)]
for m in range(1,8):
    h.append(s.expand(((m*m+2*lam)*h[m]+lam*sum(C.coeff(t,2*j)*h[m-2*j] for j in range(1,m//2+1)))/(m*(m+1))))
H=sum(x*t**j for j,x in enumerate(h))
res=s.expand(t*(1-t)*s.diff(H,t,2)-t*s.diff(H,t)-lam*C*H)
if not all(res.coeff(t,j)==0 for j in range(1,8)):
    raise RuntimeError('Frobenius formal equation failed')
L=[s.expand(sum(C.coeff(t,k)*h[j+1-k] for k in range(j+2))) for j in range(7)]
expand=1+lam*sum(L[j]*(-1)**(j+1)*s.factorial(j)*q**(j+1)/s.prod(1-i*q for i in range(j+1)) for j in range(6))
series=s.series(expand,q,0,5).removeO().expand()
rat=s.series(series/s.expand(series.subs(lam,1)),q,0,4).removeO().expand()
result={
'original_counts_n2_through18':[str(x.subs(lam,1)) for x in polys],
'marked_ODE_identity':'Exact polynomial identity for n=2..18',
'n10_polynomial':str(p.as_expr()),
'n10_sturm_degrees':[s.degree(x,lam) for x in st],
'n10_sturm_signs_minus_inf':sm,
'n10_sturm_signs_plus_inf':sp,
'n10_variations_minus_inf':var(sm),'n10_variations_plus_inf':var(sp),
'n10_real_roots':real,'n10_squarefree':True,
'H_coefficients':[str(x) for x in h[:6]],
'L_coefficients':[str(x) for x in L[:5]],
'normalized_coefficients':[str(series.coeff(q,j).factor()) for j in range(5)],
'PGF_correction_multipliers':[str(rat.coeff(q,j).factor()) for j in range(4)],
'numerical_roots_diagnostic':[str(x) for x in s.nroots(p,maxsteps=200)]}
(out/'exact_checks.json').write_text(json.dumps(result,indent=2,default=str))
print(json.dumps(result,indent=2,default=str))
