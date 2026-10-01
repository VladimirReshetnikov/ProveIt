#!/usr/bin/env python3
"""Check the complete finite table and independently redo pressure conversion."""
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
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
EXPECTED=[12,18,24,32,38,44,52,58,64,72,78,84,92,98,104,110,118,124,130]
def mul(a,b,N):
    c=[F(0)]*(N+1)
    for i,x in enumerate(a[:N+1]):
        if x:
            for j,y in enumerate(b[:N+1-i]):
                if y:c[i+j]+=x*y
    return c
count=0
for m,want in zip(range(2,21),EXPECTED):
    data=json.loads((ROOT/f"m{m:03d}.json").read_text())
    N=5*m
    if data["m"]!=m or data["checked_through_degree"]!=2*N:
        raise ArithmeticError("coverage")
    V=list(map(F,data["normalized_eigenvalue_even_coefficients"]))
    P=list(map(F,data["pressure_even_coefficients"]))
    if len(V)!=N+1 or len(P)!=N+1 or V[0]!=1:raise ArithmeticError("dimensions")
    Q=[F(0)]*(N+1)
    for k in range(1,N+1):
        Q[k]=V[k]-sum(F(i,k)*Q[i]*V[k-i] for i in range(1,k))
    T=[F(0)]*(N+1);T[0]=1
    for k in range(1,N+1):T[k]=sum(T[i]*T[k-1-i] for i in range(k))/F(2*k+1)
    T2=mul(T,T,N)
    powers=[F(0)]*(N+1);powers[0]=1
    result=[F(0)]*(N+1)
    for j in range(1,N+1):
        powers=mul(powers,T2,N)
        if Q[j]:
            for k in range(j,N+1):result[k]+=Q[j]*powers[k-j]
    for k in range(1,N+1):result[k]-=F(m,k)*T[k-1]
    if result!=P:raise ArithmeticError(f"conversion m={m}")
    if P[1]!=-m or P[m]!=0:raise ArithmeticError("low coefficients")
    if not all(P[k]>0 for k in range(m+1,3*m)):raise ArithmeticError("positive window")
    first=next((2*k for k in range(m+1,N+1) if P[k]<0),None)
    if first!=want or first!=data["first_post_cancellation_negative_degree"]:raise ArithmeticError("first negative")
    count+=N+1
summary={"passed":True,"orders":list(range(2,21)),"pressure_coefficients_recomputed":count,"fourier_orders_in_exact_production":sum(10*m for m in range(2,21)),"first_negative_degrees":EXPECTED}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('table_validation.json', json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary))

