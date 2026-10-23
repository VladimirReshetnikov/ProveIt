#!/usr/bin/env python3
"""Exact sparse integer-polynomial identities for the delivered evaluators."""
import json
from pathlib import Path

class Poly:
    dim=8
    def __init__(self,data):self.data={k:v for k,v in data.items()if v}
    @classmethod
    def lift(cls,x):return x if isinstance(x,cls)else cls({(0,)*cls.dim:x})
    @classmethod
    def var(cls,i):
        t=[0]*cls.dim;t[i]=1;return cls({tuple(t):1})
    def __add__(self,o):
        d=dict(self.data)
        for k,v in self.lift(o).data.items():d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.data.items()})
    def __sub__(self,o):return self+-self.lift(o)
    def __rsub__(self,o):return self.lift(o)+-self
    def __mul__(self,o):
        d={}
        for a,v in self.data.items():
            for b,w in self.lift(o).data.items():
                k=tuple(x+y for x,y in zip(a,b));d[k]=d.get(k,0)+v*w
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        r=self.lift(1)
        for i in range(n):r=r*self
        return r

def check(v,msg):
    if not v: raise ValueError(msg)

def monic_symbolic():
    B,W,v,c,u,t,r1=[Poly.var(i) for i in range(7)]
    oldR=v*v+B*(r1*t)**2-c*(u*u+B*r1*r1)
    oldI=2*(v*r1*t-c*u*r1)
    old=oldR**2-B*oldI**2
    J=B*r1*r1
    newR=v*v+J*t*t-c*(u*u+J)
    new=newR**2-4*J*(v*t-c*u)**2
    check(not (old-new).data,'12 norm polynomial identity')
    check(not (B*(2*W)**2-4*B*W**2).data,'compressed square identity')
    h=Poly.var(7);old13=h*h-B*(r1*t)**2;new13=h*h-J*t*t
    check(not (old13-new13).data,'13 norm identity')
    return ['12-variable norm refactor: exact symbolic identity','13-variable norm refactor: exact symbolic identity','r1=2W square reuse: exact symbolic identity']
def nested_symbolic():
    C,d,k,r,Z,G,V1=[Poly.var(i) for i in range(7)]
    # Quadratic pairs use sqrt(G) in old expression, V1*sqrt(G) in new.
    x=C*C+G*(d*V1)**2-k*r-Z;y=2*C*d*V1-k*V1
    oldR=x*x+G*y*y-4*Z*k*r;oldI=2*x*y-4*Z*k*V1
    old=oldR**2-G*oldI**2
    J=G*V1*V1;xx=C*C+J*d*d-k*r-Z;yy=2*C*d-k
    newR=xx*xx+J*yy*yy-4*Z*k*r;newI=2*xx*yy-4*Z*k
    new=newR**2-J*newI**2
    check(not(oldR-newR).data,'real identity')
    check(not(oldI-V1*newI).data,'imaginary factor identity')
    check(not(old-new).data,'norm identity')
    return 'Three exact sparse-integer polynomial identities; no division, so valid also when V1=0.'
def main():
    R,E,a,T,i,c,C,Z=[Poly.var(j)for j in range(8)]
    I=i*c*c
    old=1+8*T*I+16*R*E*i*i*c**3
    new=1+8*I*(T+2*R*E*i*c)
    check(not(old-new).data,'positive weight factorization')
    old=1+8*(T*I)**2+16*R*a*i*i*c**3
    new=1+8*(i*c)*I*(T*T*c+2*R*a)
    check(not(old-new).data,'signed weight factorization')
    check(not(((C-T)**2-Z)*((C+T)**2-Z)-((C*C-T*T-Z)**2-4*T*T*Z)).data,'two-root symmetric norm')
    rep,Fsum,Zsum,inner=[Poly.var(j)for j in range(4)]
    q=rep+1;F=Fsum+1;z=Zsum+1
    check(not(q-F-(rep-Fsum)).data,'F shift cancellation')
    check(not(inner+q-F-z*rep-(inner-Fsum-Zsum*rep)).data,'transport shift cancellation')
    result={'status':'PASS','method':'Full sparse-polynomial expansion over Z, all resulting coefficients equal zero. No finite sampling in this certificate.',
       'identities':monic_symbolic()+[nested_symbolic(),
       'M_positive=1+8I(T+2REic), where I=ic^2',
       'M_signed=1+8(ic)I(T^2c+2Ra), where I=ic^2',
       '((C-u)^2-Z)((C+u)^2-Z)=(C^2-u^2-Z)^2-4u^2Z',
       'q-F=rep-Fsum under q=rep+1,F=Fsum+1',
       'inner+q-F-z*rep=inner-Fsum-Zsum*rep under z=Zsum+1'],
       'scope':'These are circuit identities. The Pell/root-recovery and compiler statements require their mathematical proofs.'}
    (Path(__file__).resolve().parent.parent/'evidence'/'EXACT_IDENTITIES.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
