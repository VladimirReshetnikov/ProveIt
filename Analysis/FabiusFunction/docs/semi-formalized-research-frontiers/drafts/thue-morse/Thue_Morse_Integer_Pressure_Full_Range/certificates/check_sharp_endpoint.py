"""Independent exact three-mode determinant and pressure endpoint check."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from fractions import Fraction as F
from math import factorial
from itertools import permutations
from pathlib import Path
import json

def pmul(a,b):
    out={}
    for (i,j),x in a.items():
        for (k,l),y in b.items():out[i+k,j+l]=out.get((i+k,j+l),F(0))+x*y
    return {k:v for k,v in out.items() if v}
A=[[F(1,2),F(1,8),F(0)],[F(1,2),F(3,4),F(1,2)],[F(0),F(1,8),F(1,2)]]
det={}
for p in permutations(range(3)):
    inv=sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
    term={(0,0):F((-1)**inv)}
    for i in range(3):
        cell={(0,1-i):-A[i][p[i]]}
        if i==p[i]:cell[1,0]=F(1)
        term=pmul(term,cell)
    for k,v in term.items():det[k]=det.get(k,F(0))+v
det={k:v for k,v in det.items() if v}
expected={(3,0):F(1),(2,1):F(-1,2),(2,-1):F(-1,2),(2,0):F(-3,4),(1,1):F(5,16),(1,-1):F(5,16),(1,0):F(1,4),(0,0):F(-1,8)}
assert det==expected
N=6
c=[F((-1)**j*4**j,factorial(2*j))for j in range(N+1)]
u=[F(1)]+[F(0)]*N
def mul(a,b):return [sum((a[j]*b[k-j]for j in range(k+1)),F(0))for k in range(N+1)]
for n in range(1,N+1):
    u2=mul(u,u);u3=mul(u2,u);cu2=mul(c,u2);cu=mul(c,u)
    residual=u3[n]-cu2[n]-F(3,4)*u2[n]+F(5,8)*cu[n]+F(1,4)*u[n]
    u[n]=-F(8,3)*residual
res=[a-b-F(3,4)*c+F(5,8)*d+F(1,4)*e for a,b,c,d,e in zip(mul(mul(u,u),u),mul(c,mul(u,u)),mul(u,u),mul(c,u),u)]
res[0]-=F(1,8);assert not any(res)
p=[F(0)]*(N+1)
for n in range(1,N+1):p[n]=u[n]-sum((F(j,n)*p[j]*u[n-j]for j in range(1,n)),F(0))
assert p[1:]==[F(-2),F(0),F(376,45),F(6836,189),F(105448,2025),F(-35360872,93555)]
out={'all_checks_passed':True,'m':2,'coefficients':{str(2*j):str(p[j])for j in range(1,N+1)},'determinant_verified':True,'series_residual_verified':True}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('sharp_endpoint_certificate.json', json.dumps(out,indent=2)+'\n')
print('Exact m=2 endpoint verified:',p[6])
