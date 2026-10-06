#!/usr/bin/env python3
"""NONCERTIFIED Fatou-coordinate quadrature. Optional NumPy and SciPy required."""
import argparse
import json
import math
from pathlib import Path
import numpy as np
from scipy.integrate import simpson

from coordinate_series import KNOWN
from fractions import Fraction
COEFFICIENTS=[float(Fraction(x)) for x in KNOWN]

def parameter(s,depth):
    target=s-depth;v=-2/target
    for _ in range(8):
        phi=-2/v+np.log(v)/3;dp=2/v**2+1/(3*v)
        for j,c in enumerate(COEFFICIENTS,1):
            phi+=c*v**j;dp+=j*c*v**(j-1)
        v-=(phi-target)/dp
    dp=2/v**2+1/(3*v)
    for j,c in enumerate(COEFFICIENTS,1): dp+=j*c*v**(j-1)
    derivative=1/dp
    for _ in range(depth):
        derivative*=np.exp(v);v=np.expm1(v)
    return v,derivative

def evaluate(depth,sigma,cutoff,step):
    if not isinstance(depth,int) or isinstance(depth,bool) or not 50<=depth<=200:
        raise ValueError('depth must be an integer from 50 to 200')
    if not all(math.isfinite(v) for v in (sigma,cutoff,step)):
        raise ValueError('finite numeric parameters required')
    if not -2<=sigma<=0 or not 10<=cutoff<=10000 or not .005<=step<=.1:
        raise ValueError('use sigma in [-2,0], cutoff in [10,10000], step in [.005,.1]')
    intervals=int(round(cutoff/step))
    if intervals%2: intervals+=1
    if intervals>1000000: raise ValueError('at most 1000000 quadrature intervals supported')
    t=np.linspace(0,cutoff,intervals+1);s=sigma+1j*t
    _,derivative=parameter(s,depth)
    integrand=np.real((derivative-2/(1-s)**2)*np.exp(-1j*t))
    h1=2/math.e+math.exp(-sigma)/math.pi*float(simpson(integrand,x=t))
    T=math.pi/2;B=.5-math.pi/6-math.pi**2/16-math.log(2)/6
    c=T**(1/3)*math.exp(-B)*h1
    if not math.isfinite(c): raise ArithmeticError('nonfinite diagnostic')
    return {'status':'NONCERTIFIED floating-point diagnostic; no interval or digit guarantee',
            'depth':depth,'sigma':sigma,'cutoff':cutoff,'intervals':intervals,
            'actual_step':cutoff/intervals,'h1':h1,'c':c}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=100);ap.add_argument('--sigma',type=float,default=0)
    ap.add_argument('--cutoff',type=float,default=3000);ap.add_argument('--step',type=float,default=.02)
    ap.add_argument('--out',help='optional NEW JSON file; otherwise stdout only')
    args=ap.parse_args()
    try: result=evaluate(args.depth,args.sigma,args.cutoff,args.step)
    except ValueError as exc: ap.error(str(exc))
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:
        # Exclusive create refuses existing files, including existing symlinks.
        with Path(args.out).open('x') as stream: stream.write(output)
    print(output,end='')

if __name__=='__main__': main()
