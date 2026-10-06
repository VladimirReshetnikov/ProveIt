#!/usr/bin/env python3
"""Independent exact full-polynomial, scalar and inverse-series checks."""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import factorial
import sys
sys.dont_write_bytecode=True
import sympy as s
from common import emit, new_file_path, require, validated_wick_receipt
from formal_factorization import cumulant, cell_product
from small_gaussian import cumulant_from_moments, moment_n1, moment_n2, laurent_evaluate
from inverse_reversion import check_reversion
from density_coefficients import check_density, check_cm_comparison


def receipt():
    data=validated_wick_receipt()
    z=s.Symbol('z')
    direct=s.series(-s.I*z-s.log(2-s.exp(s.I*z))+z*z,z,0,9).removeO().expand()
    coefficients={d:s.simplify(direct.coeff(z,d)/s.I**d) for d in range(3,9)}
    expected={str(d):str(v) for d,v in coefficients.items()}
    require(expected==data['coefficients'],'independent geometric log series mismatch')
    rows=[]; log=defaultdict(Q)
    for row in data['rows']:
        ds=tuple(row['degrees'])
        require(row['cost']==sum(d-2 for d in ds)//2,'diagram cost mismatch')
        computed=cumulant(ds)
        expected={int(k):Q(v) for k,v in row['cumulant'].items()}
        require(computed==expected,'independent full Laurent identity mismatch')
        weight=s.I**sum(ds)
        for d in ds:weight*=coefficients[d]
        for count in Counter(ds).values():weight/=factorial(count)
        weight=Q(str(weight))
        require(weight==Q(row['weight']),'independent logarithm weight mismatch')
        tests={}
        for n,moment in ((1,moment_n1),(2,moment_n2)):
            result=cumulant_from_moments(ds,moment)
            require(result==laurent_evaluate(row['cumulant'],n),'independent small-n cumulant mismatch')
            tests[str(n)]=str(result)
        for power,value in computed.items(): log[power]+=weight*value
        rows.append({'degrees':list(ds),'entire_laurent_identity':'PASS',
                     'formal_product_monomials':len(cell_product(ds)),
                     'independent_small_n_cumulants':tests})
    final={str(p):str(v) for p,v in sorted(log.items(),reverse=True) if p>=-2 and v}
    require(final=={'0':'1/4','-1':'-3/2','-2':'223/32'},'independent aggregate mismatch')
    require(final==data['log_through_n_minus_2'],'coefficient receipt aggregate mismatch')
    return {'status':'PASS','independent_geometric_log_coefficients':{str(d):str(v) for d,v in coefficients.items()},
            'rows':rows,'log_through_n_minus_2':final,'inverse_reversion':check_reversion(),
            'density_coefficients':check_density(),
            'canfield_mckay_comparison':check_cm_comparison(),
            'scope':'Exact finite algebra; does not certify localization, analytic remainders, novelty or numerical inverse error.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(receipt(),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
