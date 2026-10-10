#!/usr/bin/env python3
"""220-digit Mellin-integral diagnostic for the unproved S6 conjecture.

Requires mpmath. Uses the same frozen integer vector as certify_s6.py and
series_crosscheck.py. Numerical agreement alone is not a proof of equality.
"""
import json
import argparse
from pathlib import Path
import mpmath as mp

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('s6_mellin_check.json'),
                    help='Destination JSON file (default: beside this script).')
args=parser.parse_args()

mp.mp.dps=220
COEFFICIENTS=[485683200,-665395200,-36864000,401080320,
              -258247,11750400,109347840,971366400]
NAMES=['S6','g61','g43','g25','pi^7','G*zeta(5)','beta(4)*zeta(3)','beta(6)*log(2)']
PATH=[0,mp.mpf('.25'),mp.mpf('.75'),1]

def g(a,b):
    return mp.im(mp.quad(lambda x:(-mp.log(x))**(a-1)*1j*mp.polylog(b,1j*x)/(1-1j*x),PATH)/mp.factorial(a-1))
S6=-mp.quad(lambda x:(-mp.log(x))**5*mp.log(1+x*x)/(1+x*x),PATH)/mp.factorial(5)
values=[S6,g(6,1),g(4,3),g(2,5),mp.pi**7,mp.catalan*mp.zeta(5),
        mp.im(mp.polylog(4,1j))*mp.zeta(3),mp.im(mp.polylog(6,1j))*mp.log(2)]
residual=mp.fsum(c*v for c,v in zip(COEFFICIENTS,values))
assert abs(residual)<mp.mpf('1e-205')
report={'claim':'Numerical diagnostic only; S6 remains a conjecture',
        'precision':mp.mp.dps,'mpmath_version':mp.__version__,
        'coefficients':COEFFICIENTS,'ordered_basket':NAMES,
        'values':[str(x) for x in values],'integer_normalized_residual':str(residual)}
output=args.output
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(report,indent=2)+'\n')
print('Integer-normalized residual:',mp.nstr(residual,50))
print(output)
