"""Independent general-a verification of the final Mellin manuscript."""
import json,time
from pathlib import Path
import mpmath as mp
mp.mp.dps=30
OUT=(Path(__file__).resolve().parents[1] / 'results' / 'general_master_checks.json')

def q_coeffs(N,a):
    co=[mp.mpf(1)]
    for k in range(1,N):
        new=[mp.mpf(0)]*(len(co)+1)
        for j,c in enumerate(co):
            new[j]+=(a-k)*c
            new[j+1]+=c
        co=new
    return [c/mp.factorial(N-1) for c in co]

def rhs(N,a,s,z):
    q=N-a
    def L(u):
        if z==1:return mp.zeta(u,q)-mp.zeta(u)
        return z**q*mp.lerchphi(z,u,q)-mp.polylog(u,z)
    return (-1)**N*mp.pi/mp.sin(mp.pi*a)*mp.fsum(c*L(s-j) for j,c in enumerate(q_coeffs(N,a)))

def lhs(N,a,s,z):
    def f(t):
        if t==0 or t==1:return 0
        return t**(a-1)*(1-t)**(N-a-1)*mp.polylog(s,-z*t/(1-t))
    return mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.75'),1])

cases=[(2,'-.3','.15','.4'),(3,'1.4','.2','1'),(5,'3.2','-.15','.4'),(5,'2.6','.25','1')]
rows=[]
for N,ar,ai,zr in cases:
    a=mp.mpc(ar,ai); s=mp.mpc('.7','.25');z=mp.mpf(zr)
    st=time.monotonic();l=lhs(N,a,s,z);r=rhs(N,a,s,z)
    err=abs(l-r)/max(1,abs(l),abs(r))
    row=dict(N=N,a=str(a),s=str(s),z=str(z),integral=str(l),master=str(r),scaled_error=str(err),seconds=round(time.monotonic()-st,2))
    rows.append(row);OUT.write_text(json.dumps(dict(dps=mp.mp.dps,rows=rows),indent=2))
    print(N,str(a),str(z),mp.nstr(err,8),row['seconds'],flush=True)
    assert err<mp.mpf('1e-22')
print('PASS',len(rows),'general-master checks',flush=True)
