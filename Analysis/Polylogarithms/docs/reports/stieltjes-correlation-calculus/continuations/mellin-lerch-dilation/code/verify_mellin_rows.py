"""Independent quadrature checks of Mellin--Lerch integer rows.
Uses no Lerch evaluation in the integrals.  Evidence, not a substitute for proof.
"""
import json, time
from pathlib import Path
import mpmath as mp
mp.mp.dps=28
OUT=(Path(__file__).resolve().parents[1] / 'results' / 'mellin_rows.json')

def q_coeffs(N,a):
    co=[mp.mpf(1)]
    for k in range(1,N):
        new=[mp.mpf(0)]*(len(co)+1)
        for j,c in enumerate(co):
            new[j]+=(a-k)*c
            new[j+1]+=c
        co=new
    return [c/mp.factorial(N-1) for c in co]

def J_formula(N,m,s,z):
    ell=mp.log(z)
    return (-1)**(N+m)*mp.fsum(c*((s-j)*mp.polylog(s-j+1,z)-ell*mp.polylog(s-j,z)) for j,c in enumerate(q_coeffs(N,m)) if c)

def J_quad(N,a,s,z):
    def fun(t):
        if t==0 or t==1:return 0
        return t**(a-1)*(1-t)**(N-a-1)*mp.polylog(s,-z*t/(1-t))
    return mp.quad(fun,[0,mp.mpf('.25'),mp.mpf('.75'),1])

def valstr(v): return str(v)
rows=[]
def run(N,m,s,z,kind):
    start=time.monotonic()
    lhs=J_quad(N,m,s,z)
    rhs=J_formula(N,m,s,z)
    err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
    row=dict(kind=kind,N=N,m=m,s=valstr(s),z=valstr(z),integral=valstr(lhs),formula=valstr(rhs),scaled_error=valstr(err),seconds=round(time.monotonic()-start,2))
    rows.append(row)
    OUT.write_text(json.dumps(dict(dps=mp.mp.dps,rows=rows),indent=2))
    print(kind,N,m,s,z,mp.nstr(err,6),row['seconds'],flush=True)
    assert err<mp.mpf('1e-23')

# Every integer Mellin row at the three requested kernel orders, including
# zero and negative spectral orders and both sides of the individual cuts.
for N in (2,3,5):
    for m in range(N):
        run(N,m,[0,-1,-2][m%3],mp.mpf('.4') if m%2==0 else mp.mpf('2'),'integer_s')
# Complex spectral orders at the endpoint and middle Mellin rows.
for N,m,z in [(2,0,'.4'),(2,1,'2'),(3,1,'.4'),(3,2,'2'),(5,0,'2'),(5,2,'.4'),(5,4,'2')]:
    run(N,m,mp.mpc('.7','.25'),mp.mpf(z),'complex_s')
print('PASS',len(rows),'checks',flush=True)
