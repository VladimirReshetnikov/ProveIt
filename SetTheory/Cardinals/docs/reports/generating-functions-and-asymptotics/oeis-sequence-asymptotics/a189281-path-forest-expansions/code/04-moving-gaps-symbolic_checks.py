#!/usr/bin/env python3
"""Optional exact symbolic checks (requires SymPy); writes general B_1 and B_2."""
from pathlib import Path
from math import factorial
import sympy as s

def main():
    a,b,c,d,e,f,t,u=s.symbols('a b c d e f theta u')
    # a,c,e are source densities; b,d,f are target densities.
    # Use the exact profile loop directly so theta remains a symbolic variable.
    from local_expansions import normalized_tilings, stats, conv, inverse_falling, pfact
    A=normalized_tilings([a,c,e,0],4,2)
    B=normalized_tilings([b,d,f,0],4,2)
    R=[[s.Integer(0)]*5 for _ in range(3)]
    for p in A.keys() & B.keys():
        k,C,v=stats(p); defect=k-C
        if defect>2: continue
        z=conv(conv(A[p],B[p],2),inverse_falling(v,2),2)
        for j in range(defect,3): R[j][k]+=t**C*pfact(p)*z[j-defect]
    lam=t*a*b
    BP=[]
    for j in range(3):
        coeff=[s.expand(sum(R[j][k]*(-lam)**(q-k)/factorial(q-k)
                           for k in range(q+1))) for q in range(5)]
        assert all(z==0 for z in coeff[2*j+1:])
        BP.append(coeff)
    C=2*lam**2-t**2*(a*a*(b+2*d)+b*b*(a+2*c))/2+t*c*d
    assert s.expand(BP[1][1]-lam)==0
    assert s.expand(BP[1][2]-C)==0
    assert s.expand(BP[2][4]-C**2/2)==0
    # Highest-path sensitivity for q=3.
    H3=t*f-2*t*t*b*d+t**3*b**3
    assert s.expand(s.diff(BP[2][3],e)-H3)==0
    assert all(s.diff(BP[2][j],e)==0 for j in [0,1,2,4])
    # Factorized log-G second-order coefficients.
    D=s.expand(BP[2][2]-lam**2/2)
    E=s.expand(BP[2][3]-lam*C)
    AA, BB = a+2*c, b+2*d
    RR, SS = a+6*c+3*e, b+6*d+3*f
    expected_D = t**2*(22*a*a*b*b-6*(a*a*BB+b*b*AA)+AA*BB)/2+3*t*c*d
    expected_E = (t**3*(s.Rational(28,3)*a**3*b**3
                    -4*a*b*(a*a*BB+b*b*AA)+a*b*AA*BB
                    +(a**3*SS+b**3*RR)/3)
                  +t*t*(6*a*b*c*d-2*a*c*(d+f)-2*b*d*(c+e))+t*e*f)
    assert s.expand(D-expected_D)==0
    assert s.expand(E-expected_E)==0
    expected_B2 = [0, lam, expected_D+lam**2/2,
                   expected_E+lam*C, C**2/2]
    assert all(s.expand(x-y)==0 for x,y in zip(BP[2],expected_B2))
    text=['Exact symbolic identities: PASS',
          'Notation: a=S1(P)/n, c=S2(P)/n, e=S3(P)/n;',
          '          b=S1(V)/n, d=S2(V)/n, f=S3(V)/n.',
          'lambda = theta*a*b', 'C = '+str(s.expand(C)),
          'B1 = lambda*u+C*u**2',
          'B2 = lambda*u+(D+lambda**2/2)*u**2+(E+lambda*C)*u**3+C**2/2*u**4',
          'D = '+str(s.factor(D)), 'E = '+str(s.factor(E)),
          'd(B2)/de = u**3*(theta*f-2*theta**2*b*d+theta**3*b**3)',
          'B2 quartic coefficient = C**2/2: PASS',
          'Compact invariant formulas for D and E, and every B2 coefficient: PASS']
    out=Path(__file__).resolve().parents[1]/'data'
    out.mkdir(exist_ok=True)
    (out/'symbolic_coefficients.txt').write_text('\n'.join(text)+'\n')
    (out/'symbolic_coefficients.tex').write_text(
        '\\begin{align*}\nD={}&'+s.latex(s.collect(D,t))+'\\\\\nE={}&'+s.latex(s.collect(E,t))+'\n\\end{align*}\n')
    print('\n'.join(text))

if __name__=='__main__': main()
