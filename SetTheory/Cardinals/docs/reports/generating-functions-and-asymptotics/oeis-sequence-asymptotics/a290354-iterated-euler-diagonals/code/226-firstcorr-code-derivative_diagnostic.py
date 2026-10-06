#!/usr/bin/env python3
"""NONCERTIFIED density-derivative and first-correction diagnostics.

Requires NumPy and SciPy. Uses the P''' inversion with a subtracted rational
kernel and exact coefficients from coordinate_series.py. This is floating-point
quadrature, without interval bounds or certified digits. Coefficients are
analytically specified, never fitted. Public exact414.json is the comparison
source. Output is JSON on stdout; --out exclusively creates a new file.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
from pathlib import Path
import numpy as np
from scipy.integrate import simpson
from coordinate_series import KNOWN

ROOT = Path(__file__).resolve().parents[1]
COEFFICIENTS = [float(Fraction(value)) for value in KNOWN]
GRID = [(70,1000,.02),(100,3000,.02),(150,3000,.02),(100,3000,.01),(100,10000,.02)]
T = math.pi/2
B = .5-math.pi/6-math.pi**2/16-math.log(2)/6
D0 = math.log(T)/3-B
CATALAN = .91596559417721901505
KAPPA = math.pi**3/96+math.pi**2/12-13*math.pi/48-11/36-CATALAN/6-math.pi*math.log(2)/24


def validate(depth,cutoff,step):
    if isinstance(depth,bool) or not isinstance(depth,int) or not 50<=depth<=200:
        raise ValueError('depth must be an integer from 50 to 200')
    for value in (cutoff,step):
        if isinstance(value,bool) or not isinstance(value,(int,float)) or not math.isfinite(value):
            raise ValueError('finite real numeric cutoff and step required')
    if not 10<=cutoff<=10000 or not .005<=step<=.1:
        raise ValueError('cutoff must be in [10,10000] and step in [.005,.1]')
    intervals = int(round(cutoff/step))
    if intervals%2:
        intervals += 1
    if intervals>1000000:
        raise ValueError('at most 1000000 quadrature intervals supported')
    return intervals


def parameter_third(s,depth):
    """Numerical P,P',P'',P''' from a truncated inverse Fatou coordinate."""
    target = s-depth
    value = -2/target
    for _ in range(9):
        phi = -2/value+np.log(value)/3
        first = 2/value**2+1/(3*value)
        for j,coefficient in enumerate(COEFFICIENTS,1):
            phi += coefficient*value**j
            first += j*coefficient*value**(j-1)
        value -= (phi-target)/first
    first = 2/value**2+1/(3*value)
    second = -4/value**3-1/(3*value**2)
    third = 12/value**4+2/(3*value**3)
    for j,coefficient in enumerate(COEFFICIENTS,1):
        first += j*coefficient*value**(j-1)
        if j>=2:
            second += j*(j-1)*coefficient*value**(j-2)
        if j>=3:
            third += j*(j-1)*(j-2)*coefficient*value**(j-3)
    d1 = 1/first
    d2 = -second/first**3
    d3 = 3*second**2/first**5-third/first**4
    for _ in range(depth):
        exponential = np.exp(value)
        d3 = exponential*(d3+3*d1*d2+d1**3)
        d2 = exponential*(d2+d1**2)
        d1 = exponential*d1
        value = np.expm1(value)
    return value,d1,d2,d3


def evaluate(depth=100,cutoff=3000,step=.02):
    intervals = validate(depth,cutoff,step)
    times = np.linspace(0,cutoff,intervals+1)
    s = 1j*times
    _,_,_,d3 = parameter_third(s,depth)
    remainder = d3-12/(1-s)**4
    oscillation = np.exp(-s)
    inverted = []
    # These are g(1),g'(1),g''(1) for g(x)=x^3 h(x).
    # The three exact subtracted-kernel inverse values are 2/e,4/e,2/e.
    for order,main in enumerate((2/math.e,4/math.e,2/math.e)):
        integral = simpson(np.real((-s)**order*remainder*oscillation),x=times)
        inverted.append(main+float(integral)/math.pi)
    h = inverted[0]
    hp = inverted[1]-3*h
    hpp = inverted[2]-6*hp-6*h
    if not all(math.isfinite(value) for value in (h,hp,hpp)) or h<=0:
        raise ArithmeticError('nonfinite or nonpositive density diagnostic')
    rho1,rho2 = hp/h,hpp/h
    c = T**(1/3)*math.exp(-B)*h
    log_coefficient = D0/3+4/9+rho1/3
    constant_coefficient = -D0*D0/2-D0*(4/3+rho1)-T*KAPPA-1/3-4*rho1/3-rho2/2
    return {'depth':depth,'cutoff':cutoff,'intervals':intervals,'actual_step':cutoff/intervals,
            'h1':h,'hprime1':hp,'hsecond1':hpp,'rho1':rho1,'rho2':rho2,'kappa':KAPPA,
            'c':c,'log_squared_coefficient':-1/18,'log_coefficient':log_coefficient,
            'constant_coefficient':constant_coefficient}


def comparisons(row,indices=(20,40,60,80,100,150,200,250,300,350,400,414)):
    data = json.loads((ROOT/'data/exact414.json').read_text())
    values = data['diagonal']
    result = []
    for n in indices:
        if isinstance(n,bool) or not isinstance(n,int) or not 1<=n<len(values):
            raise ValueError('comparison indices must be integers from 1 to 414')
        # Decimal avoids converting a >640-digit integer under the low Python
        # string limit. This normalization is still a NONCERTIFIED diagnostic.
        with localcontext() as context:
            context.prec = 70
            nd = Decimal(n)
            td = Decimal('1.570796326794896619231321691639751442098584699687552910487472296154')
            scaled = float((Decimal(values[n]).ln()-nd*(nd/td).ln()+Decimal(4)*nd.ln()/3).exp())
        logn = math.log(n)
        polynomial = -logn*logn/18+row['log_coefficient']*logn+row['constant_coefficient']
        prediction = row['c']*(1+polynomial/n)
        result.append({'n':n,'exact_integer_normalized_noncertified':scaled,
                       'first_correction_prediction':prediction,'residual':scaled-prediction,
                       'n_times_relative_residual':n*(scaled/row['c']-1)-polynomial})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth',type=int,default=100)
    parser.add_argument('--cutoff',type=float,default=3000)
    parser.add_argument('--step',type=float,default=.02)
    parser.add_argument('--grid',action='store_true',help='run the five stated sensitivity settings')
    parser.add_argument('--out',help='optional NEW JSON file; otherwise stdout only')
    args = parser.parse_args()
    try:
        rows = ([evaluate(*parameters) for parameters in GRID] if args.grid
                else [evaluate(args.depth,args.cutoff,args.step)])
        result = {'status':'NONCERTIFIED; floating-point quadrature, no interval bounds or guaranteed digits',
                  'method':'P third-derivative inversion; rational-tail subtraction; analytic coefficients, no fitting',
                  'scope':'Parameter variation and exact-integer comparisons are diagnostics, not proofs',
                  'rows':rows,'comparison_row':len(rows)-1,'exact_comparisons':comparisons(rows[-1])}
    except ValueError as exc:
        parser.error(str(exc))
    output = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:
        with Path(args.out).open('x') as stream:
            stream.write(output)
    print(output,end='')


if __name__ == '__main__':
    main()
