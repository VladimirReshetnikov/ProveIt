#!/usr/bin/env python3
"""Independent symbolic Laurent substitution for the sharp cubic constant.
No producer import or sampled activity evaluation.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import argparse,hashlib,json
import check

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
rows=(8,4,0,0,0)
code=sum(1 << a for a,(i,j) in enumerate(check.ARCS) if rows[i] >> j & 1)
gamma=check.construct_gammas(code,rows)
# Variables carry (rational coefficient, epsilon exponent). Zeros kill terms.
values=[(1,1),(1,1),(0,0),(0,0),(1,0),
        (0,0),(0,0),(1,-1),(1,-1),(0,0),
        (Fraction(1,2),0),(Fraction(1,2),0)]
univariate=[]
for polynomial in gamma:
    out=defaultdict(Fraction)
    for packed,coefficient in polynomial.items():
        power=0;value=Fraction(coefficient)
        for unit,(scalar,degree) in zip(check.UNIT,values):
            exponent=(packed//unit)%check.RADIX
            value*=scalar**exponent
            power+=degree*exponent
        if value:
            out[power]+=value
    univariate.append(dict(out))
expected=[{0:1},{0:3,1:2},{0:3,1:Fraction(5,2),2:Fraction(1,4)},
          {0:1,1:Fraction(1,2)}]
check.require(univariate==expected,'Symbolic gamma formulas differ')
gap=defaultdict(Fraction)
for e,c in univariate[2].items():
    for f,d in univariate[2].items():gap[e+f]+=c*d
for e,c in univariate[1].items():
    for f,d in univariate[3].items():gap[e+f]-=3*c*d
gap={e:c for e,c in gap.items() if c}
check.require(gap=={1:Fraction(9,2),2:Fraction(19,4),3:Fraction(5,4),4:Fraction(1,16)},
              'Symbolic gap differs')
check.require(univariate[3][0]>0 and all(c>=0 for c in univariate[3].values()),
              'Actual degree three not established for epsilon>0')
ratio=univariate[2][0]**2/(univariate[1][0]*univariate[3][0])
check.require(ratio==3,'Wrong sharp limiting ratio')
receipt={'status':'PASS','core_rows':list(rows),'method':'Symbolic exact Laurent substitution into independent literal/Hall gamma polynomials; no sampled activities',
         'gamma_polynomials':[{str(k):str(v) for k,v in sorted(p.items())} for p in univariate],
         'cubic_gap':{str(k):str(v) for k,v in sorted(gap.items())},
         'actual_degree_three_for_every_positive_epsilon':True,
         'limiting_gamma':'(1+t)^3','limiting_ratio':str(ratio),
         'sharpness_inference':'No universal coefficient greater than 3 can replace 3 in gamma2^2 >= 3 gamma1 gamma3, even for this two-internal-arc core with two sinks',
         'producer_code_imported_or_executed':False,
         'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'support_checker_sha256':hashlib.sha256(Path(check.__file__).read_bytes()).hexdigest()}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
