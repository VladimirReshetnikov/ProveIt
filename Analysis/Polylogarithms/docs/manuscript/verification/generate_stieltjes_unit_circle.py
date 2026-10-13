"""Generate rational certificates for the unit-circle classification, 1<=q<=8.

Uses the real Cayley-coordinate recurrence, rational linear algebra, and
univariate extended Euclid. No Groebner basis or numerical root search is used.
The independent verifier rebuilds the original-color recurrence instead.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
import sympy as sp

HERE=Path(__file__).resolve().parent
ORDER_BOUND=8
b,t,X,Y,a=sp.symbols('b t X Y a',real=True)

def require(condition,message):
    if not bool(condition): raise ValueError(message)

def squared_polynomial(expression):
    polynomial=sp.Poly(sp.cancel(expression),b,t,domain=sp.QQ)
    require(all(i%2==0 and j%2==0 for (i,j),coefficient in polynomial.terms()),
            'Parity decomposition is not polynomial in b^2,t^2')
    return sp.factor(sum(coefficient*X**(i//2)*Y**(j//2)
                         for (i,j),coefficient in polynomial.terms()))

def unit_certificate(polys,variables,degree_limit=6):
    for degree in range(degree_limit+1):
        monomials=sorted(sp.itermonomials(variables,degree),
                         key=lambda value:(sp.total_degree(value),str(value)))
        columns=[sp.Poly(p*m,*variables,domain=sp.QQ) for p in polys for m in monomials]
        powers=sorted(set.union({tuple(0 for _ in variables)},*(set(p.monoms()) for p in columns)))
        matrix=sp.Matrix([[p.coeff_monomial(power) for p in columns] for power in powers])
        target=sp.Matrix([int(all(value==0 for value in power)) for power in powers])
        try:
            solution,parameters=matrix.gauss_jordan_solve(target)
        except ValueError:
            continue
        solution=solution.subs({parameter:0 for parameter in parameters})
        multipliers=[sp.factor(sum(solution[i*len(monomials)+j]*m
                         for j,m in enumerate(monomials))) for i in range(len(polys))]
        require(sp.expand(sum(c*p for c,p in zip(multipliers,polys))-1)==0,
                'Constructed multiplier identity failed direct expansion')
        return {'multipliers':list(map(str,multipliers)),'degree_bound':degree}
    raise ValueError('No unit certificate within the explicit finite search bound')

def generate():
    B=[sp.Integer(1)]
    for k in range(ORDER_BOUND):
        B.append(sp.expand((b+sp.I*t/2)*B[-1]+sp.I*(1+t*t)*sp.diff(B[-1],t)/2))
    R=[squared_polynomial(sp.re(value)/(b if k%2 else 1)) for k,value in enumerate(B)]
    I=[squared_polynomial(sp.im(value)/(t*(b if k%2==0 else 1))) for k,value in enumerate(B)]
    polynomials=[{'k':k,'R':str(R[k]),'I':str(I[k])} for k in range(ORDER_BOUND+1)]
    records=[]
    for q in range(1,ORDER_BOUND+1):
        noncentral=unit_certificate([R[q-1],I[q-1],R[q],I[q]],(X,Y))
        central=unit_certificate([(R[j] if j%2==0 else I[j]).subs(X,0)
                                 for j in (q-1,q)],(Y,))
        e0,e1=sp.euler(q-1,a),sp.euler(q,a)
        m0,m1,g=sp.gcdex(e0,e1,a)
        require(sp.expand(m0*e0+m1*e1-g)==0,'Euler Bezout construction failed')
        require(sp.rem(e0,g,a)==0 and sp.rem(e1,g,a)==0,'Euler common divisibility failed')
        expected=a*a-a-1 if q==5 else sp.Integer(1)
        require(sp.expand(g-expected)==0,'Unexpected Euler gcd in the bounded classification')
        records.append({'q':q,'noncentral':noncentral,'central':central,
                        'alternating':{'gcd':str(g),'multipliers':[str(m0),str(m1)]}})
        print(f"q={q}: noncentral degree {noncentral['degree_bound']}, central degree {central['degree_bound']}, gcd {g}",flush=True)
    return {'schema_version':1,'max_order':ORDER_BOUND,
            'scope':'1<=q<=8, a>0, abs(omega)=1, omega!=1; no higher-order claim',
            'polynomials':polynomials,'certificates':records}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'stieltjes-unit-circle-certificates.json')
    args=parser.parse_args()
    data=generate()
    args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print('PASS: generated all 8 order certificates without a Groebner calculation')
    return 0

if __name__=='__main__':
    sys.exit(main())
