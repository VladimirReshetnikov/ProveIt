"""Independent exact linear-solve audit; no producer code imported."""
from pathlib import Path
from fractions import Fraction
from math import factorial
import json
import sympy as s
x,t,l=s.symbols('x t l'); c=s.Rational(2,3); V=c*x+l
Z=(s.S.Zero,s.S.Zero)
def plus(*us): return tuple(s.expand(sum(u[i] for u in us)) for i in (0,1))
def scale(q,u): return tuple(s.expand(q*a) for a in u)
def deriv(u): return (s.expand(s.diff(u[0],x)+V*u[1]),s.expand(u[0]+s.diff(u[1],x)))
def cut(q,m): return s.series(q,t,0,m+1).removeO().expand()
def shifted(u,arg,m):
    d=arg-x; out=Z
    for k in range(m+1):
        out=plus(out,scale(cut(d**k,m)/s.factorial(k),u)); u=deriv(u)
    return tuple(cut(q,m) for q in out)
def residual(profiles,mus,mode,m):
    minus=1-c*x*t**2/(1+x*t**2-t**3)
    if mode=='frozen':
        bm=cut(s.sqrt(minus),m); bp=cut(s.sqrt(1-c*(x+t)*t**2/(1+x*t**2)),m)
        am=x-t; ap=x+t
    else:
        bm=cut(minus,m); bp=1
        dilation=cut((1-t**3)**(-s.Rational(1,3)),m)
        am=cut((x-t)*dilation,m); ap=cut((x+t)*dilation,m)
    out=Z
    for k,u in enumerate(profiles):
        q=t**k
        if mode!='frozen': q*=cut((1-t**3)**(-s.Rational(k,3)),m-k)
        out=plus(out,scale(q,plus(scale(bm,shifted(u,am,m-k)),scale(bp,shifted(u,ap,m-k)))))
    out=plus(out,scale(-2-sum(a*t**i for i,a in mus.items()),tuple(sum(t**k*u[i] for k,u in enumerate(profiles)) for i in (0,1))))
    return tuple(cut(q,m) for q in out)
def derive(mode):
    profiles=[(s.S.One,s.S.Zero)]; mus={2:l}
    records=[]
    for m in range(3,8):
        base=residual(profiles,mus,mode,m)
        R,S=[s.expand(q).coeff(t,m) for q in base]
        k=m-2; deg=2*k
        pp=s.symbols('p:'+str(deg+1)); qq=s.symbols('q:'+str(deg+1)); mu=s.Symbol('mu')
        P=sum(a*x**i for i,a in enumerate(pp)); Q=sum(a*x**i for i,a in enumerate(qq))
        # Direct coefficient equations, avoiding the producer triangular inverse.
        eqF=s.diff(P,x,2)+2*V*s.diff(Q,x)+c*Q-mu+R
        eqFp=2*s.diff(P,x)+s.diff(Q,x,2)+S
        eqs=s.Poly(eqF,x).all_coeffs()+s.Poly(eqFp,x).all_coeffs()+[Q.subs(x,0),P.subs(x,0)+s.diff(Q,x).subs(x,0)]
        sol=s.solve(eqs,pp+qq+(mu,),dict=True)
        assert len(sol)==1 and all(v in sol[0] for v in pp+qq+(mu,))
        mu0=s.factor(sol[0][mu]); u=tuple(s.factor(q.subs(sol[0])) for q in (P,Q))
        profiles.append(u); mus[m]=mu0
        records.append({'order':m,'full_scalar':str(mu0),'P':str(u[0]),'Q':str(u[1])})
        print(mode,m,mu0,u,flush=True)
    assert all(q==0 for q in residual(profiles,mus,mode,7))
    # Endpoint directly from ODE Taylor coefficients.
    fs=[s.S.Zero,s.S.One]
    for j in range(2,10): fs.append(s.expand((l*fs[j-2]+(c*fs[j-3] if j>=3 else 0))/(j*(j-1))))
    f=sum(a*x**i for i,a in enumerate(fs)); fp=s.diff(f,x)
    end=cut(sum(t**k*(u[0]*f+u[1]*fp).subs(x,t) for k,u in enumerate(profiles))/t,4)
    ans={'records':records,'residual_identically_zero_through':7,'endpoint_over_t':str(end)}
    if mode=='nonautonomous':
        h1,h2,h3,h4=s.symbols('h1 h2 h3 h4'); hs=(h1,h2,h3,h4)
        logratio=cut(3*(l/2)/t*(1-(1-t**3)**s.Rational(1,3))-(mus[3]/2)*s.log(1-t**3)+sum(h*t**i*(1-(1-t**3)**(-s.Rational(i,3))) for i,h in enumerate(hs,1)),7)
        target=cut(s.log(1+sum(v*t**k/2 for k,v in mus.items())),7)
        sol=s.solve([s.expand(logratio-target).coeff(t,j) for j in (4,5,6,7)],hs,dict=True)[0]
        logend=cut(s.log(end),4)
        logs=[s.factor(sol[h]+logend.coeff(t,i)) for i,h in enumerate(hs,1)]
        ans['log_H']={str(h):str(sol[h]) for h in hs};ans['log_endpoint_correction_N']=list(map(str,logs))
    return ans
report={mode:derive(mode) for mode in ('frozen','nonautonomous')}
# Exact recurrence and Q-ratio checks on a fresh small triangle.
A=[[1]]
for n in range(1,25):
    row=[(2*n-1)*A[-1][0]]
    for k in range(1,n+1):row.append(row[-1]+(2*n+k-1)*(A[-1][k] if k<n else 0))
    A.append(row)
def d(N,j):
    if j<0 or j>N or (N+j)%2:return Fraction(0)
    n=(N+j)//2;k=(N-j)//2
    return Fraction(A[n][k],3**n*factorial(n))
def g2(N,j):
    q=Fraction(1)
    for k in range(1,j+1):q*=Fraction(3*N+k-2,3*(N+k))
    return q
count=0
for N in range(1,25):
    for j in range(N%2,N+1,2):
        assert d(N,j)==d(N-1,j+1)+Fraction(3*N+j-2,3*(N+j))*d(N-1,j-1);count+=1
qcount=0
for N in range(2,25):
    for j in range(N+2):
        q=Fraction(N+j,N)
        for r in (2,3,4):q*=Fraction(3*N-r,3*N+j-r)
        assert q==g2(N-1,j)/g2(N,j) and 0<q<=1;qcount+=1
report['exact_checks']={'recurrence_instances':count,'gauge_instances':qcount,'diagonal_prefix':[r[-1] for r in A[:9]]}
Path(__file__).with_name('independent-order7-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
