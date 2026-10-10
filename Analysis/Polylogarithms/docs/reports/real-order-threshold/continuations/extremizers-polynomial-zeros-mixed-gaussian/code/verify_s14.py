"""Recompute the exact rational 10^-775 proximity certificate for S14.

This program reads only the frozen integer vector, not numerical values.
Default execution also compares both residual endpoints to the shipped
certificate.  The result proves proximity; it does not prove equality.
"""
import argparse, json, sys, time
from pathlib import Path
from math import gcd
from functools import reduce
from fractions import Fraction as Q
from mixed_gaussian_common import ExactEuler, Interval, elementary_intervals

sys.set_int_max_str_digits(1000000)
BASE=Path(__file__).resolve().parents[1]


def verify(write=False):
    start=time.monotonic()
    frozen=json.loads((BASE/'data/s14_candidate.json').read_text())
    vector=frozen['vector']
    if not (frozen['p']==14 and len(vector)==16 and vector[0]>0):
        raise ValueError('Expected the positive-first, 16-term S14 vector')
    if reduce(gcd,vector)!=1:
        raise ValueError('The frozen S14 vector must be primitive')
    if vector[-1]!=2*vector[0]:
        raise ValueError('The final S14 coefficient must equal twice the first')
    e=ExactEuler(2600)
    pi,log2=elementary_intervals(650,950)
    vals=[e.mixed(14)]+[e.gaussian(a,15-a) for a in range(14,1,-2)]
    vals += [pi**15]
    vals += [e.beta(2*j)*e.zeta(15-2*j) for j in range(1,7)]
    vals += [e.beta(14)*log2]
    residual=sum((v*Q(c,vector[0]) for v,c in zip(vals,vector)),Interval(0))
    bound=Q(1,10**775)
    if not (-bound<residual.lo<=0<=residual.hi<bound):
        raise ArithmeticError('S14 residual must contain zero and lie strictly '
                              'inside (-10^-775, 10^-775)')
    record=dict(frozen)
    record.update({'Euler_terms':2600,'arctangent_terms_each':650,
                   'logarithm_terms':950,
                   'arithmetic':'Python integers and fractions.Fraction only',
                   'normalized_residual':residual.record(),
                   'basket_intervals':[x.record() for x in vals],
                   'proved_absolute_bound':'10^-775','contains_zero':True})
    path=BASE/'data/s14_rational_certificate.json'
    if write:
        path.write_text(json.dumps(record,indent=2)+'\n')
    else:
        shipped=json.loads(path.read_text())
        if shipped['vector']!=vector:
            raise ValueError('The shipped certificate has a different S14 vector')
        if shipped['normalized_residual']!=record['normalized_residual']:
            raise ArithmeticError('S14 residual endpoints differ from the '
                                  'shipped certificate')
        if shipped['basket_intervals']!=record['basket_intervals']:
            raise ArithmeticError('S14 basket intervals differ from the '
                                  'shipped certificate')
    print(json.dumps({'result':'Exact rational replay passed',
                      'normalized_absolute_residual':'<10^-775',
                      'interval_contains_zero':True,
                      'equality_status':'conjectural',
                      'seconds':round(time.monotonic()-start,3)},indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',
                        help='Regenerate the certificate instead of comparing it')
    verify(parser.parse_args().write)
