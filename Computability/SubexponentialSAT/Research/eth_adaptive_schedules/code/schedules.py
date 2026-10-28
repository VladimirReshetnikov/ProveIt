#!/usr/bin/env python3
"""Exact parameter generators for the new contraction schedules.

These are schedule generators, not a contraction or SAT solver. Positive taper
alone is not a finite-input feasibility certificate. The contractor must check
actual padded mass, degree/precision interfaces, and its direct-sum fallbacks.
The input is lambda=ceil(log2(s)); this module never constructs s=2**lambda.
"""
from fractions import Fraction
import argparse, json

_PS_ALPHABETS=(13,14,8,6,5,4)
_PS_TAPERS=(Fraction(27,2000),Fraction(51,4000),Fraction(141,20000),
            Fraction(53,10000),Fraction(11,2500),Fraction(69,10000))
_FAST_ALPHABETS=(7,9)
_FAST_TAPERS=(Fraction(89,5000),Fraction(137,10000))

def _integer(value, name, minimum):
    if isinstance(value,bool) or not isinstance(value,int) or value<minimum:
        raise ValueError(f'{name} must be an integer >= {minimum}')

def _taper(depth, family):
    if family=='polynomial':
        if depth<6: return _PS_ALPHABETS[depth],_PS_TAPERS[depth]
        return 3,Fraction(131,40000)*Fraction(3,4)**(depth-6)
    if family=='cached':
        if depth<2: return _FAST_ALPHABETS[depth],_FAST_TAPERS[depth]
        return 6,Fraction(923,250000)*Fraction(12,25)**(depth-2)
    raise ValueError('family must be polynomial or cached')

def schedule_from_lambda(lam, depth, family='polynomial'):
    """Return exact r,u,a,g; input lam is log-size, not actual network size.

    a is the sum of every prior floored taper plus (depth+1)*g, not the
    floor of the cumulative ideal taper. This distinction matters near zero.
    """
    _integer(lam,'lam',1); _integer(depth,'depth',0)
    if family not in ('polynomial','cached'):
        raise ValueError('family must be polynomial or cached')
    g=((lam-1).bit_length())**2
    cumulative=0
    for j in range(depth+1):
        r,t=_taper(j,family)
        u=(lam*t.numerator)//t.denominator
        cumulative+=u
    return {'family':family,'lambda':lam,'depth':depth,'r':r,'u':u,
            'a':cumulative+(depth+1)*g,'g':g,
            'taper_positive':u>0,
            'finite_feasibility':'requires actual packing, degree and precision checks'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('lam',type=int,help='ceil(log2(s)), without constructing s')
    parser.add_argument('depth',type=int)
    parser.add_argument('--family',choices=('polynomial','cached'),default='polynomial')
    args=parser.parse_args()
    print(json.dumps(schedule_from_lambda(args.lam,args.depth,args.family),indent=2))
if __name__=='__main__': main()
