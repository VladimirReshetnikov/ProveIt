#!/usr/bin/env python3
"""Finite symbolic checks of the displayed correction formulas."""
from pathlib import Path
import json
import sympy as s

def main():
    e=s.symbols('e')
    M,J,b,b0=s.symbols('M J b b0',nonzero=True)
    V=2*J+M-M**2
    delta=e/M+(J/M**3-1/(2*M))*e**2
    assert s.simplify(s.expand(1-M*delta+J*delta**2-s.exp(-e).series(e,0,3).removeO()).coeff(e,2))==0
    logroot=s.series(-s.log(1-delta),e,0,3).removeO()
    assert s.simplify(logroot.coeff(e,2)-V/(2*M**3))==0
    amplitude=s.series((b/delta+b0)/(M-V*delta),e,0,1).removeO()
    d=b*(-s.Rational(1,2)+1/M+J/M**2)+b0/M
    assert s.simplify(amplitude-b/e-d)==0
    q=s.symbols('q')
    c1=-2*q/(1-q)
    assert s.simplify((c1-1)/(1-q**2)+1/(1-q)**2)==0
    t,A,h=s.symbols('t A h')
    series=sum(s.Rational(k**(k-1),s.factorial(k))*A**k*h**(k-1)*t**k for k in range(1,7))
    residual=s.series(series-A*t*s.exp(h*series),t,0,7).removeO()
    assert s.expand(residual)==0
    result={'status':'PASS','checks':[
      'critical root expansion through epsilon^2',
      'logarithmic root coefficient V/(2M^3)',
      'critical moving-residue constant d',
      'second coefficient of the exact q-product tail',
      'Lambert-W top-degree coefficients through order six'],
      'scope':'Finite exact symbolic identities, not a proof of asymptotic remainder bounds.'}
    out=Path(__file__).resolve().parent.parent/'data'/'symbolic_checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
