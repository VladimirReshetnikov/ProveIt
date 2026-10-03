#!/usr/bin/env python3
"""Independent characteristic-polynomial check of finite pressure coefficients."""
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

from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json, sympy as s
ROOT=Path(__file__).resolve().parent
z,lam=s.symbols("z lam")
def conv(a,b,N):
    out=[F(0)]*(N+1)
    for i,x in enumerate(a[:N+1]):
        if x:
            for j,y in enumerate(b[:N+1-i]):
                if y:out[i+j]+=x*y
    return out
rows=[]
for m in range(2,7):
    N=5*m; ids=list(range(1-m,m)); q=len(ids)
    A=s.Matrix([[s.binomial(2*m,m+2*k-r)/2**(2*m-1) for r in ids] for k in ids])
    T=s.diag(*[z**(-k) for k in ids])*A
    cp=s.Poly(T.charpoly(lam).as_expr(),lam)
    cs=[]
    for j in range(q+1):
        coeff=[F(0)]*(N+1)
        for term in s.Add.make_args(s.expand(cp.nth(j))):
            power=int(term.as_powers_dict().get(z,0)); a=term/z**power
            a=F(int(s.numer(a)),int(s.denom(a)))
            for n in range(N+1):coeff[n]+=a*F((-1)**n*(2*power)**(2*n),factorial(2*n))
        cs.append(coeff)
    rho=[F(1)]+[F(0)]*N
    derivative=sum(j*cs[j][0] for j in range(1,q+1))
    if derivative==0:raise ArithmeticError("root not simple")
    for n in range(1,N+1):
        powers=[[F(1)]+[F(0)]*n]
        for j in range(q):powers.append(conv(powers[-1],rho,n))
        residual=sum(sum(cs[j][h]*powers[j][n-h] for h in range(n+1)) for j in range(q+1))
        rho[n]=-residual/derivative
    pressure=[F(0)]*(N+1)
    for n in range(1,N+1):
        pressure[n]=rho[n]-sum(F(j,n)*pressure[j]*rho[n-j] for j in range(1,n))
    reference=json.loads((ROOT/f"m{m:03d}.json").read_text())
    stored=list(map(F,reference["pressure_even_coefficients"]))
    if pressure!=stored:raise ArithmeticError(f"pressure mismatch at m={m}")
    first=next(2*k for k in range(m+1,N+1) if pressure[k]<0)
    if first!=reference["first_post_cancellation_negative_degree"]:raise ArithmeticError("first mismatch")
    rows.append({"m":m,"exact_coefficients_compared":N+1,"first_negative_degree":first})
    print(rows[-1],flush=True)
if F(json.loads((ROOT/"m002.json").read_text())["pressure_even_coefficients"][6])!=F(-35360872,93555):
    raise ArithmeticError("m2 endpoint mismatch")
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('independent_charpoly_checks.json', json.dumps({"passed":True,"rows":rows,"total_coefficients":sum(r["exact_coefficients_compared"] for r in rows)},indent=2)+"\n")

