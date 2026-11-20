#!/usr/bin/env python3
"""Exact witness checks for the rational Euler producer; not an iPRA proof."""
from fractions import Fraction as F
import json
from pathlib import Path


def vadd(a,b): return tuple(x+y for x,y in zip(a,b))
def vsub(a,b): return tuple(x-y for x,y in zip(a,b))
def smul(s,a): return tuple(s*x for x in a)
def matvec(a,x): return tuple(sum((aij*xj for aij,xj in zip(row,x)),F(0)) for row in a)
def msub(a,b): return tuple(tuple(x-y for x,y in zip(ar,br)) for ar,br in zip(a,b))
def vnorm(x): return max(map(abs,x),default=F(0))
def mnorm(a): return max((sum(map(abs,row),F(0)) for row in a),default=F(0))
def B(t): return ((t,F(1)),(F(-1),F(0)))

def euler(b,n,v):
    out=[v]
    for j in range(n): out.append(vadd(out[-1],smul(F(1,n),matvec(b(F(j,n)),out[-1]))))
    return out

def polygon(b,x,t):
    n=len(x)-1
    if t==1: return x[-1]
    j=(t.numerator*n)//t.denominator
    return vadd(x[j],smul(t-F(j,n),matvec(b(F(j,n)),x[j])))

def dot(a,b): return sum((x*y for x,y in zip(a,b)),F(0))
def clearance(u,h,s):
    a=vsub(u,s); E=dot(h,h); D=dot(a,h)
    tau=F(0) if E==0 else max(F(0),min(F(1),-D/E))
    q=vadd(a,smul(tau,h)); return tau,dot(q,q)


def cadd(a,b): return (a[0]+b[0],a[1]+b[1])
def csub(a,b): return (a[0]-b[0],a[1]-b[1])
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cscale(x,a): return (x*a[0],x*a[1])
def cnorm(a): return abs(a[0])+abs(a[1])
def cinv(a):
    d=a[0]*a[0]+a[1]*a[1]
    assert d>0
    return (a[0]/d,-a[1]/d)
def cmatnorm(a): return max(sum(cnorm(x) for x in row) for row in a)
def cmatdiff(a,b): return tuple(tuple(csub(x,y) for x,y in zip(ar,br)) for ar,br in zip(a,b))
def ceilq(x): return -(-x.numerator//x.denominator)
def gauss_matrix(u,h,params,t):
    a,b,c=params; one=(F(1),F(0)); zero=(F(0),F(0))
    z=cadd(u,cscale(t,h)); inv=cinv(cmul(z,csub(one,z)))
    q=cmul(cmul(a,b),inv)
    p=cmul(csub(cmul(cadd(cadd(a,b),one),z),c),inv)
    return ((zero,h),(cmul(h,q),cmul(h,p)))
def gauss_bounds(u,h,A):
    one=(F(1),F(0)); zero=(F(0),F(0))
    _,mu0=clearance(u,h,zero); _,mu1=clearance(u,h,one)
    assert mu0>0 and mu1>0
    R=max(cnorm(u),cnorm(cadd(u,h))); T=cnorm(h)
    D=R*(1+R)/(mu0*mu1); S=2*A+1
    Q=A*A; P=S*R+A; N=Q+P
    K=ceilq(T*(1+N*D))
    L=ceilq(T*T*(S*D+N*D*D*(1+2*R)))
    J=ceilq(T*D*(2*A+2*R+1))
    return K,L,J

def run():
    K,L,U=2,1,1
    G=3**K; H=(L+K*K)*G*U; C=G*H
    v=(F(1),F(0)); data=[]; total=0
    for n in (1,2,3,5,8,13,16):
        coarse=euler(B,n,v); fine=euler(B,2*n,v); delta=F(1,2*n)
        maximum=F(0)
        for j in range(2*n):
            t=F(j,2*n); V=polygon(B,coarse,t); Vnext=polygon(B,coarse,t+delta)
            actual=vsub(vsub(Vnext,V),smul(delta,matvec(B(t),V)))
            if j%2==0: expected=(F(0),F(0))
            else:
                x=coarse[j//2]; before=t-delta
                expected=smul(delta,vsub(matvec(msub(B(before),B(t)),x),smul(delta,matvec(B(t),matvec(B(before),x)))))
            assert actual==expected
            assert vnorm(actual)<=delta*delta*H
            total+=2
        for j in range(6*n+1):
            t=F(j,6*n)
            a=polygon(B,coarse,t); b=polygon(B,fine,t)
            assert vnorm(a)<=G*U
            assert vnorm(vsub(a,b))<=F(C,2*n)
            maximum=max(maximum,vnorm(vsub(a,b))); total+=2
        data.append({'n':n,'max_sampled_refinement_error':str(maximum),'proved_bound':str(F(C,2*n))})
    # The common-mesh coefficient perturbation identity and stability estimate.
    eta=F(1,16)
    def Bt(t): return ((t+eta,F(1)),(F(-1),eta))
    K2=3; G2=3**K2
    for n in (2,4,8,16):
        x=euler(B,n,v); y=euler(Bt,n,v)
        for j in range(n+1):
            assert vnorm(vsub(x[j],y[j]))<=G2*G2*eta
            assert mnorm(msub(B(F(j,n)),Bt(F(j,n))))==eta
            total+=2
    # Exact clearance exercises interior projection, both endpoints, and a hit.
    cases=[((F(1,2),F(0)),(F(0),F(1,3)),(F(0),F(0))),
           ((F(-1),F(1)),(F(2),F(0)),(F(0),F(0))),
           ((F(1),F(1)),(F(1),F(0)),(F(0),F(0))),
           ((F(-2),F(1)),(F(1),F(0)),(F(0),F(0))),
           ((F(-1),F(0)),(F(2),F(0)),(F(0),F(0)))]
    checks=[]
    for u,h,s in cases:
        tau,mu=clearance(u,h,s)
        for k in range(101):
            q=vsub(vadd(u,smul(F(k,100),h)),s)
            assert dot(q,q)>=mu; total+=1
        checks.append({'u':list(map(str,u)),'h':list(map(str,h)),'tau':str(tau),'minimum_squared_distance':str(mu),'passes':mu>0})
    # Exact complex-rational Gauss coefficient and parameter bounds.
    params=((F(1,2),F(0)),(F(1,3),F(1,4)),(F(1),F(0)))
    changed=((F(1,2)+F(1,32),F(0)),(F(1,3),F(1,4)-F(1,32)),(F(1),F(1,32)))
    A=2; eps=F(1,32); gauss=[]
    for u,h in [((F(1,2),F(0)),(F(0),F(1,4))),
                ((F(1,2),F(1,4)),(F(1,4),F(0))),
                ((F(-1),F(1,4)),(F(3,2),F(0)))]:
        Kb,Lb,Jb=gauss_bounds(u,h,A)
        for r in range(5):
            t=F(r,4); bt=gauss_matrix(u,h,params,t)
            assert cmatnorm(bt)<=Kb; total+=1
            btilde=gauss_matrix(u,h,changed,t)
            assert cmatnorm(cmatdiff(bt,btilde))<=Jb*eps; total+=1
            for ss in range(5):
                st=F(ss,4); bs=gauss_matrix(u,h,params,st)
                assert cmatnorm(cmatdiff(bt,bs))<=Lb*abs(t-st); total+=1
        gauss.append({'u':list(map(str,u)),'h':list(map(str,h)),'K':Kb,'L':Lb,'J':Jb})
    return {'status':'passed','meaning':'Exact finite witness checks; not a kernel-checked iPRA derivation.','gauss_bounds':gauss,
            'assertions':total,'constants':{'K':K,'L':L,'U':U,'G':G,'H':H,'C':C},'refinement':data,'clearance':checks}

if __name__=='__main__':
    report=run()
    target=Path(__file__).with_name('ode_exact_checks.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'assertions':report['assertions'],'output':str(target)}))
