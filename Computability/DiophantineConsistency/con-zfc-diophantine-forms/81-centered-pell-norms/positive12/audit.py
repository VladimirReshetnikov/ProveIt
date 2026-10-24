#!/usr/bin/env python3
"""Exact finite audit of P12/78, adapted from source69. Python standard library only.

Does not import the builder. Polynomial cuts avoid enormous expansion of
the final product, while checking all cut identities exactly over Z.
"""
import gzip
import hashlib
import json
import math
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def require(ok,label):
    if not ok:raise RuntimeError(label)

packet=json.loads((ROOT/'equation.json').read_text())
witnesses=['j','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
ports=['beta','K0','MC','MF']
abstract=['dd','rr','qq','vv','nn','ii']
names=witnesses+ports+abstract
DIM=len(names);ZERO=(0,)*DIM

class Poly:
    def __init__(self,data=0):
        self.d={e:c for e,c in data.items() if c} if isinstance(data,dict) else ({ZERO:data} if data else {})
    @staticmethod
    def var(name):
        e=[0]*DIM;e[names.index(name)]=1
        return Poly({tuple(e):1})
    def __add__(self,other):
        if not isinstance(other,Poly):other=Poly(other)
        z=dict(self.d)
        for e,c in other.d.items():
            z[e]=z.get(e,0)+c
            if not z[e]:del z[e]
        return Poly(z)
    __radd__=__add__
    def __neg__(self):return Poly({e:-c for e,c in self.d.items()})
    def __sub__(self,other):return self+(-other if isinstance(other,Poly) else -Poly(other))
    def __rsub__(self,other):return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly):other=Poly(other)
        z={}
        for e,c in self.d.items():
            for f,d in other.d.items():
                g=tuple(a+b for a,b in zip(e,f));z[g]=z.get(g,0)+c*d
        return Poly(z)
    __rmul__=__mul__
    def __pow__(self,n):
        a=self;b=Poly(1)
        while n:
            if n%2:b=b*a
            n//=2
            if n:a=a*a
        return b
    def __eq__(self,other):
        if not isinstance(other,Poly):other=Poly(other)
        return self.d==other.d
    def degree(self,weights=None):
        if weights is None:weights=[1]*len(witnesses)+[0]*(DIM-len(witnesses))
        return max((sum(a*b for a,b in zip(e,weights)) for e in self.d),default=-1)
    def lead(self,weights=None):
        if weights is None:weights=[1]*len(witnesses)+[0]*(DIM-len(witnesses))
        deg=self.degree(weights)
        return Poly({e:c for e,c in self.d.items() if sum(a*b for a,b in zip(e,weights))==deg})

def evaluate_cut(cuts,output):
    needed={output}
    for name,op,x,y in reversed(packet['source']):
        if name in needed and name not in cuts:needed.update((x,y))
    env=dict(cuts)
    for name,op,x,y in packet['source']:
        if name not in needed or name in cuts:continue
        xx=env[x] if isinstance(x,str) else Poly(x)
        yy=env[y] if isinstance(y,str) else Poly(y)
        env[name]=xx+yy if op=='+' else xx-yy if op=='-' else xx*yy
    return env[output]

def h(Q,V,u):return (1-Q)*u*u+2*(1-Q)*V*u+V*V-1
def norm(d,r,Q,V,n):
    a=h(Q,V,n);b=2*(1-Q)*(n+V);A=d*a+(1-Q)*r
    return A*A-d*b*b*r,A,b

def pell(A,index):
    x,y=1,0
    for _ in range(index):x,y=A*x+(A*A-1)*y,x+A*y
    return x,y

def main():
    require(packet['witnesses']==witnesses and packet['fixed_numerals']==ports,'exact witness and port lists')
    available=set(witnesses+ports)
    for name,op,x,y in packet['source']:
        require(name not in available,'unique register '+name)
        require(op in ['+','-','*'],'division-free operation')
        require(all(isinstance(v,int) or v in available for v in [x,y]),'topological register order')
        available.add(name)
    needed={packet['output']}
    for name,op,x,y in reversed(packet['source']):
        if name in needed:needed.update((x,y))
    require(all(row[0] in needed for row in packet['source']),'every gate live')
    require(set(witnesses+ports)<=needed,'every input and port live')
    require(len(packet['source'])==packet['operations']==103,'103 binary operations')
    breakdown=dict(Counter(row[1] for row in packet['source']))
    require(breakdown=={'*':58,'+':26,'-':19},'operation breakdown')

    env={n:Poly.var(n) for n in witnesses+ports}
    j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma=(env[x] for x in witnesses)
    beta,K0,MC,MF=(env[x] for x in ports)
    J=6*j+1;q=beta*J+1;C=q-F-alpha;E=X*Y;k=eta+zeta;c=k*Y+eta
    a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y;b0=X+a*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    S=4*q*Y;U=q*S;v=k-R-1;shift=U*gamma+S*X-v
    Dstar=U*b0+H*shift;W=(q-1)*k+1;M=q**3*(q-1)
    Bt=(q*K0+X)*C-q*F
    # Old uncontracted transport expression provides an independent specification.
    T1=(q*K0+X)*C+q*(q-F-1)
    Z=M*(ell+k+q*W+r)+(q-1)*Y-q**3*W*T1
    A0=Z**2-M**2*(ell*(ell+k)+1)
    A1=Dstar**2-U**2*(1+Delta*c*c)
    f=t+1;rho=f*f-1;d=Delta*c**4;Q=Delta*rho;V=f*f*(c*T-R)-c
    direct={'A0':A0,'A1':A1,'den':d,'rho':rho,'Q':Q,'V':V}
    for label,formula in direct.items():
        actual=evaluate_cut(env,label)
        require(actual==formula,'exact literal formula '+label)
    T0=M*(k+r)+(q-1)*Y-q**3*W*Bt
    require(A0==2*M*ell*T0+T0*T0-M*M*ell*k-M*M,'first carrier cancellation')
    A1cancel=U*U*(2*a*c*X+X*X-H*c*c-1)+2*U*(a*c+X)*H*shift+H*H*shift*shift
    require(A1==A1cancel,'main carrier cancellation')
    require(A0.degree()==15 and A1.degree()==13,'exact carrier degrees')

    dd,rr,qq,vv,nn,ii=(Poly.var(x) for x in abstract)
    expected,_,_=norm(dd,rr,qq,vv,nn)
    actual=evaluate_cut({'den':dd,'rho':rr,'Q':qq,'V':vv,'n':nn},'N')
    require(actual==expected,'exact norm cut identity')
    saturated,_,_=norm(dd,dd*ii*ii,qq,vv,nn)
    require(saturated==dd*dd*h(qq,vv,nn-ii)*h(qq,vv,nn+ii),'exact strong-equation factorization')
    final=evaluate_cut({'A0':dd,'A1':rr,'N':qq},packet['output'])
    require(final==(1+dd)*(1+rr)*(1+qq)-1,'exact unit-product finalizer')
    # Exact descent norm identity over three abstract indeterminates.
    vp=(2*qq-1)*vv-2*(qq-1)*nn
    yp=(2*qq-1)*nn-2*qq*vv
    require(qq*vp*vp-(qq-1)*yp*yp==qq*vv*vv-(qq-1)*nn*nn,'Pell descent identity')

    q0=6*beta*j;k0=eta+zeta;c0=k0*Y;Del0=X*X*Y*Y;R0=q0**3*(q0-F)
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    L0=-2*q0**8*k0**2*X*Y**2*Bt0
    L1=32*q0**2*k0*X**2*Y**4*(4*q0**2*Y*gamma+q0**3*(q0-F))
    require(A0.lead()==L0 and A1.lead()==L1,'exact carrier leading forms')
    require([d.degree(),rho.degree(),Q.degree(),V.degree()]==[12,2,6,6],'norm input degrees')
    require(d.lead()==Del0*c0**4 and Q.lead()==Del0*t*t and V.lead()==-t*t*R0,'norm input leading forms')
    weights=[0]*DIM
    for name,wt in zip(abstract,[12,2,6,6,1,0]):weights[names.index(name)]=wt
    require(expected.degree(weights)==50,'weighted exact norm degree50')
    require(expected.lead(weights)==4*dd*dd*qq*qq*vv*vv*nn*nn,'weighted norm leading form')
    LN=4*Del0**4*c0**8*t**8*R0**2*n*n
    L=L0*L1*LN
    require(L.degree()==78,'product leading degree78')
    target={'j':18,'F':2,'eta':11,'X':12,'Y':23,'t':8,'n':2,'gamma':1,'alpha':1,'beta':18}
    exponent=tuple(target.get(name,0) for name in names)
    require(L.d.get(exponent)==1024*6**18,'nonzero exact coefficient independent of three ports')

    # Generic finite checks include rational-root enumeration and canonical examples.
    rational_cases=0;descent_cases=0
    for qqn in range(2,41):
        for vvn in range(1,101):
            yy2=Fraction(qqn*vvn*vvn-1,qqn-1)
            ya,ym=math.isqrt(yy2.numerator),math.isqrt(yy2.denominator)
            if ya*ya!=yy2.numerator or ym*ym!=yy2.denominator:continue
            rational_cases+=1
            yy=Fraction(ya,ym);require(yy.denominator==1,'bounded Pell rational integrality')
            vcur,ycur=vvn,yy
            while vcur>1:
                vp=(2*qqn-1)*vcur-2*(qqn-1)*ycur
                yp=(2*qqn-1)*ycur-2*qqn*vcur
                require(vp.denominator==1 and 0<abs(vp)<vcur,'strict integral descent')
                require(qqn*vp*vp-(qqn-1)*yp*yp==1,'descent preserves norm')
                require(yp.denominator==ycur.denominator,'denominator preserved')
                vcur,ycur=int(abs(vp)),abs(yp);descent_cases+=1
    # Removing adjacency invalidates the lemma: 2*1²-4*(1/2)²=1.
    require(2-4*Fraction(1,2)**2==1,'nonadjacent-coefficient negative control')
    # Omitting f=t+1 allows rho=Q=0 and a spurious zero of the local norm.
    require(norm(1215,0,0,-10,11)[0]==0,'unshifted f=1 degeneracy control')
    canonical=[]
    for A in range(2,6):
        index=3;_,cc=pell(A,index);Del=A*A-1
        ff,II=pell(A,index*cc)
        require(II%(cc*cc)==0,'canonical normalized ordinate')
        ii=II//(cc*cc);S=Del*II;chi,yy=pell(S,index)
        require(chi%S==0,'odd auxiliary quotient')
        vv=chi//S;Tnum=vv+cc+index*ff*ff
        require(Tnum%(cc*ff*ff)==0,'positive auxiliary T integral')
        TT=Tnum//(cc*ff*ff);uu=yy-vv;nn=ii+uu
        dd=Del*cc**4;rr=ff*ff-1;qq=Del*rr
        require(TT>0 and uu>0 and ii>0 and ff>1,'canonical positivity')
        require(vv==ff*ff*(cc*TT-index)-cc,'canonical V formula')
        val,AA,bb=norm(dd,rr,qq,vv,nn)
        require(val==0 and Fraction(AA,dd*bb)==ii,'norm and inverse at canonical witness')
        canonical.append({'A':A,'R':index,'c':cc,'f_bits':ff.bit_length(),'n_bits':nn.bit_length()})

    result={'status':'PASS','witnesses':12,'domain':'strictly positive integers','exact_degree':78,'residual_degrees':[15,13,50],'live_binary_operations':103,'operation_breakdown':breakdown,'exact_identities':['carrier formulas','both carrier cancellations','norm polynomial cut','norm factorization on strong equation','unit-product finalizer','Pell descent norm'],'symbolic_carrier_terms':{'A0':len(A0.d),'A1':len(A1.d)},'norm_cut_terms':len(expected.d),'leading_coefficient':'1024*(6*beta)^18','leading_monomial':'j^18 F^2 eta^11 X^12 Y^23 t^8 n^2 gamma alpha','bounded_rational_pell_cases':rational_cases,'bounded_descent_steps':descent_cases,'canonical_local_examples':canonical,'negative_controls':['nonadjacent coefficients admit nonintegral rational ordinate','omitting f shift admits rho=0 local degeneracy'],'scope':'Exact finite arithmetic checks. Shared verifier separately authenticates coefficients and reproduces circuits. The unbounded proofs and inherited semantic boundary are in the report.'}
    (ROOT/'certificates').mkdir(exist_ok=True)
    receipt='CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json'
    (ROOT/'certificates'/receipt).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
