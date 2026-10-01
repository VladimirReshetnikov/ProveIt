"""Exact Schur-complement coefficients below the third feedback cluster."""
from pathlib import Path
import json,sys,time
import sympy as s
from matrix_math import R,tan_relative_power
ROOT=Path(__file__).resolve().parents[1]/'data'

def jets(m,N):
    ix=list(range(1-m,m));n=len(ix);d=2*m
    L=s.Matrix(n,n,lambda k,r:s.Rational(s.binomial(d,m+2*ix[k]-ix[r]),2**(d-1)) if abs(2*ix[k]-ix[r])<=m else 0)
    A=s.eye(n)-L;C=A.copy();C[0,:]=s.ones(1,n);inv=C.inv()
    rhs=s.zeros(n,1);rhs[0]=1;h0=inv*rhs
    assert A*h0==s.zeros(n,1) and sum(h0)==1
    J=[L]
    for j in range(1,min(d,N)+1):
        J.append(s.Matrix(n,n,lambda k,r:L[k,r]*sum((-1)**q*s.binomial(m+2*ix[k]-ix[r],q)*s.binomial(m-2*ix[k]+ix[r],j-q)for q in range(j+1)) if L[k,r] else 0))
    f=[h0];g=[s.zeros(n,1)]
    def solve(b):
        target=b-sum(b)*h0;rhs=target.copy();rhs[0]=0;v=inv*rhs
        assert A*v==target and sum(v)==0
        return v
    for k in range(1,N+1):
        f.append(solve(sum((J[j]*f[k-j]for j in range(1,min(k,d)+1)),s.zeros(n,1))))
        g.append(solve(f[k]+sum((J[j]*g[k-j]for j in range(1,min(k,d)+1)),s.zeros(n,1))))
    ev=lambda v:sum((-1)**abs(k)*v[j]for j,k in enumerate(ix))
    assert all(ev(f[k])==ev(g[k])==0 for k in range(1,N+1,2))
    return [s.factor((-1)**j*ev(f[2*j]))for j in range(N//2+1)],[s.factor((-1)**j*ev(g[2*j]))for j in range(N//2+1)]

def run(m):
    start=time.time();F,G=jets(m,4*m-2)
    assert F[0]==R(m) and G[0]==0
    conv=lambda X,Y,n:sum(X[j]*Y[n-j]for j in range(n+1))
    K=[s.factor(conv(F,G,j)+conv(F,F,j)/2)for j in range(m)]
    E=[];pieces=[]
    for r in range(1,2*m):
        frozen=sum(F[j]*tan_relative_power(2*m+2*j,r-j)[r-j]for j in range(r+1))
        feedback=sum(K[j]*tan_relative_power(4*m+2*j,r-m-j)[r-m-j]for j in range(r-m+1))if r>=m else 0
        cos=s.Rational(m,m+r)*R(m+r)
        E.append(s.factor(frozen-feedback-cos));pieces.append({'r':r,'frozen':str(frozen),'feedback':str(feedback),'cosine':str(cos)})
    source=json.loads((ROOT/'direct_phase_reference.json').read_text())
    row=next(x for x in source['rows']if x['m']==m)
    old={x['degree']:s.Rational(x['coefficient'])for x in row['coefficients_after_missing']}
    assert E==[old[2*m+2*r]for r in range(1,2*m)]
    out={'m':m,'F':list(map(str,F)),'G':list(map(str,G)),'feedback_K':list(map(str,K)),'pressure':list(map(str,E)),'pieces':pieces,'F_signs':[int(s.sign(v))for v in F],'G_signs':[int(s.sign(v))for v in G],'pressure_signs':[int(s.sign(v))for v in E],'exact_direct_phase_comparison':True,'runtime_seconds':time.time()-start}
    (ROOT/f'schur_m{m:03}.json').write_text(json.dumps(out,indent=2)+'\n')
    print('m',m,'F signs',out['F_signs'],'G signs',out['G_signs'],'E signs',out['pressure_signs'],'seconds',round(time.time()-start,2),flush=True)

if __name__=='__main__':
    for m in map(int,sys.argv[1:] or range(2,9)):run(m)
