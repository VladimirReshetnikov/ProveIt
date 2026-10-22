#!/usr/bin/env python3
"""Independent closed-form checks against every emitted arithmetic circuit.

These exact signed/rational fixtures validate formula transcription only.
The quantified semantic theorem is a mathematical proof, not a finite test.
"""
import json
import random
from fractions import Fraction
from pathlib import Path
from build_fixed_sources import evaluate, require


def forms(v):
    J,F,alpha,t,h,i,T,s,w,tau,eta,zeta,y,Z,gamma = (
        v[n] for n in ['Jrep','F','alpha','transport_quotient','h','i',
                       'auxiliary_quotient','s','w','tau_root','eta','zeta',
                       'y_aux','Z','gamma'])
    q = v['Bm1']*J+1
    X,Y = w*q,s*q**3
    E = X*Y
    k = eta+zeta
    c = k*Y+eta
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    Dmain = X+a*c+gamma*H
    C = Z+v['W0']
    R = (q*q-Z-q*F)*(q*q-1)+(v['MC']+q*v['MF'])*J
    bound = q-F-2*Z-alpha-v['W0plus2d']
    N0 = tau*tau-X*Y*Y*(X*Y*Y+1)*k*k
    N1 = Dmain*Dmain-Delta*c*c
    Nk = k-h*E-R
    Nt = (v['Kconstant']+w)*C+q-F-t*(q-1)
    P4 = N0*N1*Nk*Nt
    Q = Delta**2*i*i*c**4
    out = dict(N0=N0,N1=N1,Nk=Nk,Nt=Nt,P4=P4,Q=Q,bound=bound,
               Delta=Delta,c=c,R=R,T=T,y=y)
    if 'f' in v:
        f=v['f']
        V=c*(T*f-1)-R*f*f
        Ns=f*f-Delta*i*i*c**4
        Na=Q*(V*V-y*y)+y*y
        Nr=Delta*(f*f-1)*(V*V-y*y)+y*y
        out.update(Ns=Ns,Na=Na,Nr=Nr,V=V)
    D=1+Delta*i*i*c**4
    b=c+R*D
    u=c*T
    A=Q*(D*u*u+b*b)-(Q-1)*y*y-1
    B=2*Q*u*b
    K=A*A-D*B*B
    P=P4*(1+bound*bound)
    out.update(D=D,b=b,A=A,B=B,K=K,P=P)
    return out


def expected(name,z):
    if name=='fixed16_product74_degree157':
        return z['Delta']*(z['P']*z['Na']*z['Ns']-1)
    if name=='fixed16_product75_degree125':
        return z['Delta']*(z['P']*z['Nr']*z['Ns']-1)
    if name=='fixed16_product76_degree113':
        return z['P']*z['Nr']*z['Ns']-1
    if name=='fixed16_sos86_degree68':
        return sum((z[n]-1)**2 for n in ['N0','N1','Nr','Nk','Nt','Ns'])+z['bound']**2
    if name=='fixed15_product82_degree295':
        return z['P']*(z['K']+1)-1
    if name=='fixed15_outer80_degree346':
        return (z['P']*(z['A']+1)-1)**2-z['D']*(z['P']*z['B'])**2
    raise ValueError(name)


def main():
    root=Path(__file__).resolve().parent
    rng=random.Random(20261022)
    records={}
    for path in sorted(root.glob('fixed*.json')):
        p=json.loads(path.read_text())
        cases=0
        for j in range(24):
            v={n:rng.randint(-3,5) for n in p['witnesses']+p['fixed_numerals']}
            if j%2:
                v={n:Fraction(a,rng.randint(1,3)) for n,a in v.items()}
            z=forms(v)
            got=evaluate(p['source'],v)
            if p['output']:
                require(got[p['output']]==expected(p['name'],z),'closed form '+p['name'])
            else:
                names=['N0','N1','Nr','Nk','Nt','Ns']
                for n,(left,right) in zip(names,p['equations'][:-1]):
                    require(got[left]-right==z[n]-1,'system factor')
                a,b=p['equations'][-1]
                require(got[a]-got[b]==z['bound'],'system loader')
            cases+=1
        records[p['name']]={'exact_signed_cases':12,'exact_rational_cases':12}
    print(json.dumps({'status':'PASS','scope':'Full emitted sources agree with independent displayed closed forms on exact algebra fixtures; no semantic/halting witness claim.',
                      'circuits':records},indent=2))


if __name__=='__main__':
    main()
