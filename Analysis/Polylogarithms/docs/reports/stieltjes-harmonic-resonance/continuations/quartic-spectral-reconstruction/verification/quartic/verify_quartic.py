"""Exact finite-cutoff algebra and independent numerical quartic diagnostics.

Run from this directory or pass its complete path to Python.
Requires sympy and mpmath.  Numerical diagnostics are not interval proofs.
"""
from pathlib import Path
import json
import sympy as s
import mpmath as mp
from quartic import B, boundary, coordinate, centered, mzv
from mzv_reduce import generate, Z2, Z3, Z5, Z7

ROOT=Path(__file__).resolve().parent
Q5=4*Z2*Z3-10*Z5
Q7=s.Rational(102,5)*Z2**2*Z3+10*Z2*Z5-s.Rational(301,4)*Z7

def cubic(j):
    if j==1:return 9*Z3-s.Rational(17,10)*Z2**2
    rat=-s.Rational(3,2*(2*j-1))*sum((2*h+1)*s.binomial(2*j-1,2*h+3)*B(2*j-4-2*h)*B(2*h) for h in range(j-1))
    rat+=s.Rational(1,4)*int(j==3)
    return 9*B(2*j-2)*Z3-s.Rational(1,2)*int(j==2)*Z2+rat

def quartic_D(j):
    if j==0:return Q7
    value=s.Rational(2,j)*sum(s.binomial(2*j,2*l)*B(2*j-2*l)*cubic(l) for l in range(1,j+1))
    if j==1:value+=Q5
    elif j==2:value-=3*Z3
    else:value+=s.Rational(2*j-5,2)*B(2*j-6)
    return s.expand(value)

def quartic_V(r):
    return s.expand(sum(s.binomial(2*r+1,2*j+1)*s.bernoulli(2*r-2*j,s.Rational(1,2))*quartic_D(j) for j in range(r+1))/(2*r+1))

def centered_coefficients(count):
    b=[s.bernoulli(2*j,s.Rational(1,2)) for j in range(count)]
    acc=[s.S.One]+[s.S.Zero]*(count-1)
    for _ in range(4):
        acc=[sum(acc[k]*b[j-k] for k in range(j+1)) for j in range(count)]
    return acc

def mpq(q):
    return mp.mpf(int(s.numer(q)))/int(s.denom(q))

def evaluate(expr):
    poly=s.Poly(expr,Z2,Z3,Z5,Z7)
    zz=[mp.zeta(k) for k in (2,3,5,7)]
    return mp.fsum(mpq(c)*mp.fprod(z**p for z,p in zip(zz,powers)) for powers,c in poly.terms())

def numerical(r,N,J,coeffs):
    A=mp.zeta(2)
    terms=[]
    for n in range(N):
        x=mp.mpf(n)+mp.mpf('0.5')
        removed=mp.fsum(mpq(coeffs[k])*x**(2*r-4-2*k) for k in range(max(0,r-1)))
        terms.append(x**(2*r)*A**4-removed)
        A-=mp.mpf(1)/(n+1)**2
    tail=mp.fsum(mpq(coeffs[k])*mp.zeta(4+2*k-2*r,mp.mpf(N)+mp.mpf('0.5')) for k in range(max(0,r-1),J))
    return mp.fsum(terms)+tail

def main():
    red,mzv_reports=generate()
    sub={mzv(i):e for i,e in red.items() if i}
    counts={'mzv_weights':mzv_reports,'coordinate_checks':0,'centered_checks':0,'boundary_checks':0,'generator_checks':0}
    for j in range(25):
        assert s.expand(coordinate(4,2*j+1).subs(sub)-quartic_D(j))==0,j
        counts['coordinate_checks']+=1
        if j>=1:
            rhs=B(2*j-6) if j>=3 else 0
            assert s.expand(2*boundary(3,2*j-1)+boundary(4,2*j+1)-rhs)==0,j
            counts['boundary_checks']+=1
    for r in range(20):
        assert s.expand(centered(4,2*r).subs(sub)-quartic_V(r))==0,r
        counts['centered_checks']+=1
    # Check D''=4 cosh(t/2) G3 + Q5 t - 2 I^2(sinh(t/2)G2)
    # using the independent inherited closed form of sinh(t/2)G2.
    for j in range(1,25):
        # coefficient of t^(2*j-1), scaled by (2*j-1)!
        from_cubic=s.Rational(2,j)*sum(s.binomial(2*j,2*l)*B(2*j-2*l)*cubic(l) for l in range(1,j+1))
        # sinh(t/2)G2=3*zeta(3)*t/2 - I^2(t E(t))/4,
        # E(t)=sum B_(2k)t^(2k)/(2k)!.
        lower=-3*Z3 if j==2 else 0
        if j>=3:lower+=s.Rational(2*j-5,2)*B(2*j-6)
        assert s.expand(quartic_D(j)-from_cubic-int(j==1)*Q5-lower)==0
        counts['generator_checks']+=1
    q7,q5=s.symbols('Q7 Q5')
    formal=[]
    for r in range(6):
        v=s.expand(quartic_V(r).subs(Z7,(s.Rational(102,5)*Z2**2*Z3+10*Z2*Z5-q7)*s.Rational(4,301)))
        v=s.expand(v.subs(Z5,(4*Z2*Z3-q5)/10))
        formal.append(v)
    matrix=s.Matrix([[s.Poly(v,q7,q5,Z2,Z3).coeff_monomial(mon) for mon in (q7,q5,Z2,Z3,Z2**2,1)] for v in formal])
    det=s.factor(matrix.det()*s.Rational(5,2)) # replace zeta(2)^2 by (5/2)zeta(4)
    assert det==s.Rational(7361,49896000)
    counts['formal_six_coordinate_determinant']=str(det)
    coeffs=centered_coefficients(60)
    # Rational extraction: coefficients of the six first centered moments.
    extraction=[5233,697660,9382304,28113792,21816576,3886080]
    assert s.expand(sum(c*quartic_V(r) for r,c in enumerate(extraction))+s.Rational(775936,3))==0
    x=s.symbols('x')
    subtraction=s.expand(sum(c*sum(coeffs[k]*x**(2*r-4-2*k) for k in range(max(0,r-1))) for r,c in enumerate(extraction)))
    assert subtraction==3886080*x**6+20521216*x**4+21456896*x**2+s.Rational(940103168,315)
    counts['rational_extraction_checks']=2
    mp.mp.dps=120
    diagnostics=[]
    for r in range(9):
        exact=evaluate(quartic_V(r))
        vals=[]
        for N,J in ((120,36),(240,54)):
            got=numerical(r,N,J,coeffs)
            error=abs(got-exact)
            vals.append({'N':N,'J':J,'value':mp.nstr(got,95),'absolute_residual':mp.nstr(error,8)})
        assert mp.mpf(vals[-1]['absolute_residual'])<mp.mpf('1e-85'),(r,vals)
        diagnostics.append({'r':r,'closed_form':str(quartic_V(r)),'reference_value':mp.nstr(exact,95),'cutoffs':vals})
    data={'scope':'Exact rational identities and non-interval high-precision diagnostics. The analytic proof, not numerical agreement, establishes the all-r theorem.','checks':counts,'diagnostics':diagnostics,'first_subtraction_coefficients':[str(x) for x in coeffs[:10]],'formal_coordinate_order':['Q7','Q5','zeta(2)','zeta(3)','zeta(4)','1'],'formal_first_six_matrix':[[str(matrix[i,j]*(s.Rational(5,2) if j==4 else 1)) for j in range(6)] for i in range(6)]}
    (ROOT/'quartic_verification.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'quartic_moments.json').write_text(json.dumps({str(r):{'sympy':str(quartic_V(r)),'latex':s.latex(quartic_V(r))} for r in range(20)},indent=2)+'\n')
    print(json.dumps(counts,indent=2))
    print('largest second-cutoff residual:',max(mp.mpf(x['cutoffs'][-1]['absolute_residual']) for x in diagnostics))
    for x in diagnostics[:4]:print('V_'+str(x['r'])+' = '+x['reference_value'])

if __name__=='__main__':main()
