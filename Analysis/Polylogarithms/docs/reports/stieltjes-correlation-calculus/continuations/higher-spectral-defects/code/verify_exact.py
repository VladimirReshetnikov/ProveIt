#!/usr/bin/env python3
"""Finite exact regressions for the algebraic parts of the article."""
from pathlib import Path
import json, platform, time
import sympy as s

ROOT=Path(__file__).resolve().parents[1]
x,t=s.symbols('x t')
counts={}
checks=[]
def check(group, label, expression):
    answer=s.cancel(s.expand(expression))
    if answer != 0:
        raise AssertionError(f'{group}: {label}: {answer}')
    counts[group]=counts.get(group,0)+1
    checks.append({'group':group,'label':label})

def main():
    started=time.time()
    for k in range(1,21):
        D=s.rf(2*x,2*k)/s.factorial(2*k)-s.rf(x,k)/s.factorial(k)
        P=x/s.Integer(k)*s.prod(1+x/j for j in range(1,k))*(s.prod(1+2*x/(2*j+1) for j in range(k))-1)
        check('double_zero_polynomials',f'duplication k={k}',D-P)
        pol=s.Poly(D,x)
        check('double_zero_polynomials',f'constant k={k}',pol.nth(0))
        check('double_zero_polynomials',f'linear k={k}',pol.nth(1))
        O=s.harmonic(2*k)-s.harmonic(k)/2
        O2=s.harmonic(2*k,2)-s.harmonic(k,2)/4
        check('harmonic_coefficients',f'd2 k={k}',pol.nth(2)-2*O/k)
        check('harmonic_coefficients',f'd3 k={k}',pol.nth(3)-2*(O*s.harmonic(k-1)+O**2-O2)/k)
        check('harmonic_coefficients',f'Gamma correction k={k}',pol.nth(3)-4*O*s.harmonic(2*k-1)/k+2*(O**2+O2)/k)
    for k in range(1,17):
        Q=s.Poly(s.cancel((1-(1-2*t)**(2*k))/(t*(1-t))),t)
        M0=sum(coef/s.Integer(j[0]+1) for j,coef in Q.terms())
        M1=sum(coef*(-1/s.Integer(j[0]+1)**2-s.harmonic(j[0]+1)/s.Integer(j[0]+1)) for j,coef in Q.terms())
        O=s.harmonic(2*k)-s.harmonic(k)/2
        O2=s.harmonic(2*k,2)-s.harmonic(k,2)/4
        check('beta_local_moments',f'J0 k={k}',M0-4*O)
        check('beta_local_moments',f'J1 k={k}',M1+4*(O**2+O2))
    for k in range(2,33):
        coeff=sum(s.Rational((-1)**k,j*(k-j)) for j in range(1,k))
        check('confluent_log_square',f'coefficient k={k}',coeff-2*(-1)**k*s.harmonic(k-1)/k)
        Q=s.Poly(s.cancel((1-t**k-(1-t)**k)/(t*(1-t))),t)
        moment=sum(coef/s.Integer(j[0]+1) for j,coef in Q.terms())
        check('confluent_log_square',f'beta moment k={k}',moment-2*s.harmonic(k-1))
    # Formal differentiation rules: D zeta'(-n)=n*zeta'(1-n)-zeta(1-n),
    # D zeta(-n)=n*zeta(1-n). Stop before reaching a singular positive index.
    for R in range(1,9):
        for h in range(8):
            c=s.factorial(h)/s.factorial(h+R)
            a1=c; a0=c*(s.harmonic(h+R)-s.harmonic(h))
            for n in range(h+R,h,-1):
                a1,a0=n*a1,n*a0-a1
            check('anchored_primitive_algebra',f'jet coefficient R={R},h={h}',a1-1)
            check('anchored_primitive_algebra',f'value coefficient R={R},h={h}',a0)
    for m in range(1,25):
        C=s.factorial(m)/s.rf(1-t,m)
        Cm=s.factorial(m-1)/s.rf(1-t,m-1)
        check('all_jet_mass_ladder',f'germ m={m}',(m-t)*C-m*Cm)
        check('all_jet_mass_ladder',f'second normalization m={m}',s.harmonic(m)-s.harmonic(m-1)-s.Rational(1,m))
    # Explicit resonance extraction at arbitrary formal jet order.
    for r in range(1,8):
        for k in range(1,7):
            D=s.Poly(s.rf(2*x,2*k)/s.factorial(2*k)-s.rf(x,k)/s.factorial(k),x)
            gs=s.symbols('g0:'+str(r))
            Laurent=1/(2*x)+sum((-2*x)**j*gs[j]/s.factorial(j) for j in range(r))
            got=s.expand(D.as_expr()*Laurent).coeff(x,r)*s.factorial(r)
            want=s.factorial(r)*(D.nth(r+1)/2+sum(D.nth(ell)*(-2)**(r-ell)*gs[r-ell]/s.factorial(r-ell) for ell in range(2,r+1)))
            check('Stieltjes_pole_jets',f'r={r},k={k}',got-want)
    data={'status':'PASS','assertions':len(checks),'groups':counts,
          'sympy_version':s.__version__,'python_version':platform.python_version(),
          'elapsed_seconds':round(time.time()-started,3),
          'meaning':'Exact finite algebra regressions, not proofs of the analytic theorems.',
          'checks':checks}
    (ROOT/'results'/'exact_results.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
