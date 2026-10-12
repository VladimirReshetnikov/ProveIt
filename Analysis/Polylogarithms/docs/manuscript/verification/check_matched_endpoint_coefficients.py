"""Matched cubic endpoint jets: finite positive coefficients versus shifted kernels.
Non-interval diagnostics, including independently repeated precision refinement.
Run from any directory; the resulting JSON is written beside this script.
"""
from pathlib import Path
import json, time
import mpmath as mp

mp.mp.dps = 65

def coefficients(n, lam, dps=65):
    with mp.workdps(dps):
        L=mp.log(n); eps=2*mp.mpf(lam)/L; s=3+eps
        z=mp.zeta(s); A=mp.zeta(s-1); D=1+2*z+3*z*z
        theta=1/(12*z); c=1/A; kap=A*A*(2+6*z)/D
        E=mp.gamma(1-eps)/((1+eps)*(1+eps/2))
        K=lambda h: h+mp.mpf('1.5') if not eps else mp.zeta(1+eps)-1/eps-mp.expm1(mp.log(E)-eps*h)/eps
        h=mp.findroot(lambda h: mp.exp(2*h)/(n*c)-K(h)-kap, mp.log(n*L*c)/2+1)
        B=mp.exp(h); q=E*B**(-eps)/(K(h)+kap)
        M=int(mp.ceil(n+B)); ell=[mp.mpf(0)]+[mp.power(k,-s) for k in range(1,M+1)]
        conv2=[mp.mpf(0)]*(M+1); conv3=conv2.copy()
        for k in range(2,M+1): conv2[k]=mp.fdot(ell[1:k],ell[k-1:0:-1])
        for k in range(3,M+1): conv3[k]=mp.fdot(ell[1:k],conv2[k-1:0:-1])
        laws=[]
        for t in [mp.mpf(0),theta]:
            cs=[(1+3*t*z*z)/(A*D),(1-3*t*z)/(A*D),(1+t)/(A*D)]
            f1=sum(cs[j]*z**(j+1) for j in range(3))
            f=[cs[0]*ell[k]+cs[1]*conv2[k]+cs[2]*conv3[k] for k in range(M+1)]
            assert all(x>0 for x in cs) and all(x>0 for x in f[1:])
            w=[k*f[k] for k in range(M+1)]
            p=[mp.exp(-n*f1)]+[mp.mpf(0)]*M
            for k in range(1,M+1): p[k]=n*mp.fdot(w[1:k+1],p[k-1::-1])/k
            laws.append(p)
        delta=6*theta/(A*D); pref=-A**3*delta*n/(6*B**3)
        rows=[]
        for target in [-1,0,1]:
            m=int(mp.nint(n+B*target)); xi=(m-n)/B
            H=lambda a: mp.exp(-xi*xi/4)*mp.pcfd(a,-xi)/mp.sqrt(2*mp.pi)
            vals=[H(3),-q/2*mp.diff(H,5,1),-q*eps/4*mp.diff(H,5,2)+q*q/8*mp.diff(H,7,2),
                  -q*eps*eps/12*mp.diff(H,5,3)+q*q*eps/8*mp.diff(H,7,3)-q**3/48*mp.diff(H,9,3)]
            exact=B*(laws[1][m]-laws[0][m])/pref
            approximations=[sum(vals[:j+1]) for j in range(4)]
            row=dict(n=n,lam=lam,m=m,xi=mp.nstr(xi,30),B=mp.nstr(B,30),q=mp.nstr(q,30),
                     scaled_difference=mp.nstr(exact,45),predictions=[mp.nstr(x,35) for x in approximations],
                     relative_errors=[mp.nstr(abs((x-exact)/exact),18) for x in approximations],
                     central_sign=bool(laws[1][m]<laws[0][m]) if not target else None,
                     scale_residual=mp.nstr(abs(B*B/(n*c)-K(h)-kap),8))
            rows.append(row)
        return rows

def main():
    rows=[]
    grid=[(256,-.5),(256,0),(256,.5),(1024,-.5),(1024,0),(1024,.5),(4096,0)]
    for n,lam in grid:
        started=time.time(); out=coefficients(n,lam); rows+=out
        print(json.dumps(dict(n=n,lam=lam,seconds=time.time()-started,rows=out)),flush=True)
    refinements=[]
    with mp.workdps(85):
        for lam in [-.5,0,.5]:
            finer=coefficients(256,lam,85)
            for a,b in zip([r for r in rows if r['n']==256 and r['lam']==lam],finer):
                # Stored finite values have 45 significant digits.
                error=abs(mp.mpf(a['scaled_difference'])-mp.mpf(b['scaled_difference']))
                assert error<mp.mpf('1e-42')
                refinements.append(dict(n=256,lam=lam,m=a['m'],absolute_difference=mp.nstr(error,12),passed=True))
    assert all(r['central_sign'] is True for r in rows if r['xi']=='0.0')
    assert all(mp.mpf(r['scale_residual'])<mp.mpf('1e-55') for r in rows)
    out=dict(passed=True,dps=65,refinement_dps=85,scope='Non-interval finite coefficient diagnostics; no monotonic error or remainder certification is asserted',records=rows,precision_refinements=refinements)
    Path(__file__).with_name('matched-endpoint-coefficients.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
