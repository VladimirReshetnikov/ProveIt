"""Exact elementary inequalities for the analytic m>=70 cutoff."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# data/rerun/ in the package, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parents[1] / 'data' / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

def sqrt_bounds(x,scale=10**16):
    n=isqrt(x.numerator*scale**2//x.denominator)
    return F(n,scale),F(n+1,scale)
bs=[];lo=hi=F(1)
for j in range(1,13):
    bs.append((lo,hi))
    _,u=sqrt_bounds(1+lo*lo);l,_=sqrt_bounds(1+hi*hi)
    lo,hi=lo/(1+u),hi/(1+l)
for lo,hi in bs:assert lo<=hi
atlo=F(4,5);athi=F(5,6)
mean_upper=sum(atlo*hi/(1+atlo*hi)for lo,hi in bs)+atlo*F(2)**(1-len(bs))
mean_lower=sum(athi*lo/(1+athi*lo)for lo,hi in bs)
assert mean_upper<1<mean_lower
# theta=(1+sqrt2)/3 <81/100; T=pi^2(4+3sqrt2)/8 <11.
assert F(143,100)**2>2
assert F(10,7)**2>2
assert F(10)*(4+3*F(10,7))/8<11
q=F(206,225);d=140
assert (1+F(81,100)*atlo)/(1+atlo)==q
threshold=(F(275,36)*16)**2*(d+2)**2*d*q**(2*d)
assert threshold<1
ratio=F(143,142)*F(281,280)*q
assert ratio<1
# C>2. For d>=140, 2 < C^d/(16 sqrt(d)) follows from 2^d>32d.
assert 2**d>32*d
out={'all_checks_passed':True,'cutoff_m':70,'tangent_intervals':[[str(a),str(b)]for a,b in bs], 'saddle_mean_at_4_over_5_upper':str(mean_upper),'saddle_mean_at_5_over_6_lower':str(mean_lower),'tail_factor_bound':str(q),'threshold_squared':str(threshold),'successive_bound_ratio':str(ratio)}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('cutoff_certificate.json', json.dumps(out,indent=2)+'\n')
print('Exact cutoff inequalities pass; saddle is between4/5 and5/6; m>=70 suffices')
