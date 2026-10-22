#!/usr/bin/env python3
"""Independent standard-library audit of the emitted positive13 circuits.

Checks exact ring identities, arithmetic ledger closure, direct expressions,
and isolated inverse fixtures. None of these finite checks decides K215.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json, random
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'data'

def require(condition,message):
    if not condition: raise ValueError(message)

def eval_dag(p,inputs):
    values=dict(inputs);known=set(values);counts=Counter()
    for n,op,a,b in p['source']:
        require(n not in known,'reused register')
        require(op in ('+','-','*'),'invalid gate')
        av=a if type(a) is int else values[a];bv=b if type(b) is int else values[b]
        values[n]=av+bv if op=='+' else av-bv if op=='-' else av*bv
        known.add(n);counts[op]+=1
    return values,counts

def direct(a):
    J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t=[a[x] for x in ['Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','eta','zeta','gamma','t']]
    beta,K,MC,MF=[a[x] for x in ['Bm1','Kconstant','MC','MF']]
    q=beta*J+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta
    aa=E+Y;H=4*aa+3;delta=aa*aa+H;dm=X+aa*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    nm=dm*dm-delta*c*c;nk=k-h*E-R;nt=(K+w)*(q-F-alpha)+q-F-z*(q-1)
    A=1+(E*k*Y)*(E*k*Y+k);I=i*c*c;D=1+delta*I*I;Q=delta*delta*I*I
    v=c*T;zz=c+R*D;d=Q-1;M=I*I+v*v
    C=d*(t*t+M*M*A)-Q*(D*v*v+zz*zz)+1;B=2*Q*v*zz
    U=C*C+D*B*B-4*d*d*t*t*M*M*A;res=U*U-D*(2*C*B)**2
    return [nm,nk,nt,res],nm*nk*nt*(1+res)-1

class Poly:
    nv=7
    def __init__(self,d):self.d={m:c for m,c in d.items() if c}
    @classmethod
    def lift(cls,x):return x if isinstance(x,cls) else cls({(0,)*cls.nv:x})
    def __add__(self,o):
        o=self.lift(o);d=self.d.copy()
        for m,c in o.d.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,o):return self+-self.lift(o)
    def __rsub__(self,o):return self.lift(o)+-self
    def __mul__(self,o):
        o=self.lift(o);d={}
        for m,c in self.d.items():
            for n,b in o.d.items():
                t=tuple(x+y for x,y in zip(m,n));d[t]=d.get(t,0)+c*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        out=self.lift(1)
        for _ in range(n):out=out*self
        return out

def generic_identities():
    vs=[]
    for j in range(7):
        m=[0]*7;m[j]=1;vs.append(Poly({tuple(m):1}))
    f,tau,y,M,Q,v,z=vs;d=Q-1;D=f*f;A=tau*tau;t=M*tau+y
    aux=Q*(v*f-z)**2-d*y*y-1
    C=d*(t*t+M*M*A)-Q*(D*v*v+z*z)+1;B=2*Q*v*z;L=2*d*t*M*tau
    U=C*C+D*B*B-4*d*d*t*t*M*M*A
    one=C+B*f-L+aux
    two=U+2*C*B*f-aux*(aux-2*L)
    three=U*U-D*(2*C*B)**2-(U+2*C*B*f)*(U-2*C*B*f)
    for p in (one,two,three):require(not p.d,'generic polynomial identity failed')
    return {'exact_sparse_integer_ring_identities':3,'formal_variables':['f','tau','y','M','Q','v','z'],'scope':'Exact root-elimination algebra; no semantic compiler assumptions checked'}

def fixtures():
    count=0
    for rho in [2,3,5]:
        Q=rho*rho;d=Q-1;chi,psi=1,0
        for n in range(1,6):
            chi,psi=rho*chi+d*psi,chi+rho*psi
            if n not in (3,5):continue
            V=-chi//rho
            require(Q*V*V-d*psi*psi==1,'auxiliary fixture')
            for f in [-3,2,4]:
                D=f*f;v=1;z=v*f-V;I=10;M=I*I+v*v
                for sign in [-1,1]:
                    y=sign*psi;tau=1000*(z+abs(y)+1);A=tau*tau;t=M*tau+y
                    C=d*(t*t+M*M*A)-Q*(D*v*v+z*z)+1;B=2*Q*v*z
                    U=C*C+D*B*B-4*d*d*t*t*M*M*A
                    require(C>0 and U*U-D*(2*C*B)**2==0,'resultant fixture')
                    fr=Fraction(-U,2*C*B);tr=Fraction(C+B*fr,2*d*t*M);yr=t-M*tr
                    require((fr,tr,yr)==(f,tau,y),'inverse fixture')
                    count+=1
    return {'isolated_signed_inverse_fixtures':count,'scope':'Root components only, not complete machine witnesses'}

def main():
    p=json.loads((HERE/'improved_weight_polynomial13_84.json').read_text())
    s=json.loads((HERE/'improved_weight_system13_78.json').read_text())
    rng=random.Random(84515);assignments=128
    for _ in range(assignments):
        inputs={v:rng.randrange(-4,6) for v in p['witnesses']+p['fixed_numerals']}
        truth,prod=direct(inputs);pv,pc=eval_dag(p,inputs);sv,sc=eval_dag(s,inputs)
        require(pv[p['output']]==prod,'direct product mismatch')
        require([sv['norm_main'],sv['norm_index'],sv['norm_transport'],sv['UU2']-sv['sixteenC2PU']]==truth,'direct system mismatch')
    require(pc==Counter({'*':49,'+':22,'-':13}),'product ledger differs')
    require(sum(sc.values())==78 and sc['*']==46,'system ledger differs')
    result={'status':'PASS','direct_signed_assignments':assignments,'product_operations':sum(pc.values()),'system_operations':sum(sc.values()),'generic':generic_identities(),'fixtures':fixtures()}
    (ROOT/'verification/positive13_independent.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
