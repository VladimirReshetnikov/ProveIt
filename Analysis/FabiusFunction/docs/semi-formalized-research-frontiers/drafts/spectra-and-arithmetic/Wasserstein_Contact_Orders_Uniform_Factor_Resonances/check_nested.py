#!/usr/bin/env python3
"""Finite regressions for nested dyadic theorem, not proof of infinite-law claims."""
from collections import defaultdict
from fractions import Fraction as F
import json
import math

# ed. (2026-10-01): the receipt printed below is also written to
# <output-dir>/nested-verification.json, by default rerun/ beside this program, with LF line
# endings (as delivered it went only to standard output, and a shell
# redirection on Windows writes CRLF). Pass --output-dir with this program's
# own directory, on a copy, to regenerate the recorded receipt.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def conv(a,b):
    out=defaultdict(F)
    for x,c in a.items():
        for y,d in b.items(): out[x+y]+=c*d
    return dict(out)

D2={-F(1,4):F(1,2),F(1,4):F(1,2)}
D4={F(j,8):F(1,4) for j in [-3,-1,1,3]}
J1=conv(D2,{-F(1,4):F(1),F(1,4):F(1)})
J2=conv(D4,{-F(1,8):F(2),F(1,8):F(2)})
J=defaultdict(F)
for d in [J1,J2]:
    for x,c in d.items(): J[x]+=c
expected={-F(1,2):F(1),-F(1,4):F(1),F(0):F(2),F(1,4):F(1),F(1,2):F(1)}
assert dict(J)==expected
assert sum(J.values())==6
assert F(3,4)*70**2+F(1,2)*(72+2048)==4735
assert F(100,49)**4/4+F(100,49)**3/2<9
assert 9+F(5,4)*5000==6259

def sinc(x): return 1.0 if x==0 else math.sin(x)/x
def p3(q): return math.prod(sinc(4*math.pi*q**k) for k in range(3,100))
P3=p3(.5)
rows=[]
for sign in [-1,1]:
    for j in range(2,8):
        d=sign*10**(-j);q=.5+d
        derivative=.25*sinc(4*math.pi*q)*sinc(4*math.pi*q*q)*p3(q)
        ratio=derivative/d**2
        rows.append({'delta':d,'derivative_over_delta_squared':ratio})
        if j==7: assert abs(ratio+2*P3)<1e-5

data={
    'status':'PASS',
    'scope':'Exact rational digit/support constants and finite floating-point product regressions; not proof-assistant verification',
    'P3_truncation_k3_to99':P3,
    'quadratic_lower_asymptotic_constant':P3/(math.pi*(1+8*math.pi)),
    'quadratic_upper_constant':6259,
    'chi_square_energy_upper_bound':4735,
    'digit_measure':{str(k):str(v) for k,v in J.items()},
    'defect_ratio_rows':rows,
    'not_computed':['optimal distance Delta2','the actual density w','chi-square integral value','second-order limiting coefficient'],
}
# ed. (2026-10-01): the receipt is also written by _ed_write (see above).
_ed_text=json.dumps(data,indent=2)
_ed_write('nested-verification.json', _ed_text+'\n')
print(_ed_text)
