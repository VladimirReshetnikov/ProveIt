#!/usr/bin/env python3
"""Independent Euler-transformed defining-series check of the S6 candidate.
This is numerical evidence, not an interval certificate or a proof.
"""
import json
import argparse
from pathlib import Path
import mpmath as mp

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('series_crosscheck.json'),
                    help='Destination JSON file (default: beside this script).')
args=parser.parse_args()

mp.mp.dps=300
terms=900

def euler_sum(values):
    """Sum the Euler transform with stable scaled finite differences."""
    row=list(values)
    result=mp.mpf(0)
    last=mp.mpf(0)
    while row:
        last=row[0]/2
        result+=last
        row=[(row[j]-row[j+1])/2 for j in range(len(row)-1)]
    return result,last

def odd_harmonic_terms(p,b,multiplier):
    harmonic=mp.mpf(0)
    previous=0
    out=[]
    for n in range(terms):
        stop=multiplier*n
        for j in range(previous+1,stop+1):
            harmonic+=mp.mpf(j)**(-b)
        previous=stop
        out.append(harmonic/mp.mpf(2*n+1)**p)
    return out

values=[];last_terms=[]
for p,b,multiplier in [(6,1,1),(6,1,2),(4,3,2),(2,5,2)]:
    val,last=euler_sum(odd_harmonic_terms(p,b,multiplier))
    values.append(val);last_terms.append(last)
    print((p,b,multiplier),mp.nstr(val,50),'last Euler term',mp.nstr(last,8),flush=True)
values.extend([mp.pi**7,mp.catalan*mp.zeta(5),
               mp.im(mp.polylog(4,1j))*mp.zeta(3),
               mp.im(mp.polylog(6,1j))*mp.log(2)])
coefficients=[485683200,-665395200,-36864000,401080320,
              -258247,11750400,109347840,971366400]
residual=mp.fsum(c*v for c,v in zip(coefficients,values))
print('Integer normalized S6 residual:',mp.nstr(residual,60),flush=True)
report={'status':'numerical evidence only','precision':mp.mp.dps,'terms':terms,
        'mpmath_version':mp.__version__,
        'ordered_basket':['S6','g61','g43','g25','pi^7','G*zeta(5)','beta(4)*zeta(3)','beta(6)*log(2)'],
        'coefficients':coefficients,'values':[str(x) for x in values],
        'last_euler_terms':[str(x) for x in last_terms],
        'integer_normalized_residual':str(residual)}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(args.output)
