"""Independent cubic certificate for the later negative m=2 pressure coefficient."""
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
from math import factorial
from pathlib import Path
import json
N=6
p=[F(0),F(-2),F(0),F(376,45),F(6836,189),F(105448,2025),F(-35360872,93555)]
def add(*polys):return [sum((v[i]if i<len(v)else 0)for v in polys)for i in range(N+1)]
def scale(v,c):return [c*x for x in v]
def mul(v,w):return [sum(v[j]*w[i-j]for j in range(i+1))for i in range(N+1)]
def exp(v):
 q=[F(1)]
 for n in range(1,N+1):q.append(sum(k*v[k]*q[n-k]for k in range(1,n+1))/n)
 return q
C=[F((-1)**j*2**(2*j),factorial(2*j))for j in range(N+1)]
rho=exp(p);rho2=mul(rho,rho);rho3=mul(rho,rho2)
res=add(rho3,scale(rho2,F(-3,4)),scale(mul(C,rho2),-1),scale(rho,F(1,4)),scale(mul(C,rho),F(5,8)),[F(-1,8)])
assert all(v==0 for v in res)
out={'variable':'u=t^2','pressure_coefficients_through_u6':list(map(str,p)),'cubic':'lambda^3-(3/4+C)lambda^2+(1/4+5C/8)lambda-1/8','C':'cos(2t)','residual_through_u6':list(map(str,res)),'simple_root_derivative_at_lambda1_C1':'3/8','coefficient_t12':'-35360872/93555','all_checks_passed':True}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('m2_negative_higher_certificate.json', json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
