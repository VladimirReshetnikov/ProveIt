"""Independent direct Gaussian differentiation and moment recurrence, orders 0..3.
No author generator is imported or executed. All tests survive Python -O.
"""
import json
from pathlib import Path
import sympy as S

z,b,M,t=S.symbols('z b M t', real=True)
I=S.I
R=S.Rational
SNAPSHOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise RuntimeError(message)

def same(x,y,message):
    require(S.simplify(x-y)==0,message)

# Cumulants are obtained by direct differentiation of the logarithmic pgf.
F=S.log(1-S.log(1-M*(S.exp(t)-1)))
ks=[S.factor(S.diff(F,t,j).subs(t,0)) for j in range(1,6)]
expected_ks=[M,M,M*(M*M+1),M*(M**3+6*M*M+1),
             M*(8*M**4+10*M**3+25*M*M+1)]
require(ks==expected_ks,'Cumulants 1..5 mismatch')
c3=S.cancel(ks[2]/M);c4=S.cancel(ks[3]/M);c5=S.cancel(ks[4]/M)

# Direct derivatives of the standard Gaussian; no Hermite routine is used.
q=S.exp(-z*z/2)
D=lambda k:S.expand(S.diff(q,z,k)/q)
G0=S.Integer(1)
G1=-z+c3*D(3)/6+z*D(2)/2
G2=z*z-z*z*D(2)/2+(c4/24+z*z/8)*D(4)+c3*z*D(5)/12+c3*c3*D(6)/72
# Hand collection of E3+E1*E2+E1^3/6-z*(E2+E1^2/2)+z^2*E1-z^3.
G3=(-z**3+z**3*D(2)/2-z**3*D(4)/8+z**3*D(6)/48
    +c5*D(5)/120+(c3*c3/72+c4/48)*z*D(6)
    +(c3*c4/144+c3*z*z/48)*D(7)
    +c3*c3*z*D(8)/144+c3**3*D(9)/1296)
# Confirm that the hand-collected G3 equals the uncollected cubic expansion.
w=S.symbols('w')
E1=c3*w**3/6+z*w*w/2
E2=c4*w**4/24+z*c3*w**3/6
E3=c5*w**5/120+z*c4*w**4/24
raw=S.Poly(S.expand(E3+E1*E2+E1**3/6-z*(E2+E1**2/2)+z*z*E1-z**3),w)
G3_uncollected=sum(co*D(mon[0]) for mon,co in raw.terms())
same(G3,G3_uncollected,'Hand-collected G3 mismatch')

# Direct multiplication of the three cubic kernel polynomials.
# A: (1+s*z)^(-1/4); B: exp(i*R); H: normalized Hankel amplitude.
A=[1,-z/4,5*z*z/S.Integer(32),-15*z**3/S.Integer(128)]
B=[1,-I*b*z*z/4,I*b*z**3/8-b*b*z**4/32,
   -5*I*b*z**4/64+b*b*z**5/32+I*b**3*z**6/384]
H=[1,-I/(16*b),I*z/(32*b)-R(9,512)/b**2,
   -3*I*z*z/(128*b)+9*z/(512*b*b)+75*I/(8192*b**3)]
K=[S.expand(sum(A[a]*B[c]*H[d] for a in range(j+1)
                 for c in range(j-a+1) for d in [j-a-c])) for j in range(4)]
K3=(-25*z**3/S.Integer(256)+5*b*b*z**5/128+45*z/(2048*b*b)
    +I*(b**3*z**6/384-75*b*z**4/512-75*z*z/(2048*b)+75/(8192*b**3)))
same(K[3],K3,'Hand-collected K3 mismatch')

# E[Z^r exp(i*b*Z)] / exp(-b^2/2), evaluated by integration-by-parts recurrence.
mm=[S.Integer(1),I*b]
for r in range(1,9): mm.append(S.expand(I*b*mm[r]+r*mm[r-1]))
def fourier_moment(p):
    return S.expand(sum(co*mm[mon[0]] for mon,co in S.Poly(S.expand(p),z).terms()))
G=[G0,G1,G2,G3]
P=[]
for j in range(4):
    integrand=sum(G[a]*K[j-a] for a in range(j+1))
    P.append(S.factor(fourier_moment(integrand)/I**j))

# Compare only after the independent derivation is complete.
ref=json.loads((SNAPSHOT/'coefficients.json').read_text())
for j,p in enumerate(P):
    for name,obj in [('coefficients.json',ref)]:
        expected=S.sympify(obj['P'][j],locals={'M':M,'b':b})
        same(p,expected,f'P{j} mismatch in {name}')
    print(f'Independent P{j}: {p}')
for j,g in enumerate(G):
    expected=S.sympify(ref['edgeworth'][j],locals={'M':M,'z':z})
    same(g,expected,f'G{j} mismatch')
print('Independent cumulants 1..5:',ks)
print('PASS: P0..P3 agree exactly with the coefficient file; G0..G3 and cumulants 1..5 agree.')
print('No floating-point arithmetic; no assert statements; no author generator executed.')
