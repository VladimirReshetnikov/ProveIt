#!/usr/bin/env python3
"""New separator for the sourced twelve-positive-variable compiler norm.

Research artifact: formulas derived from source 34 (carrier translation)
and source 37 (w shift, scalar norm evaluator), at ProveIt 22e75dd6b8.
No executable upstream imports. The fixed ports are parameters here;
an authentic complete coefficient tuple is required for Con(ZFC).
"""
import json
from pathlib import Path

VARIABLES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']
class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def op(self,o,x,y,n=None):
        key=(o,*sorted([x,y],key=str)) if o in '+*' else (o,x,y)
        if key in self.cache:return self.cache[key]
        n=n or 'r'+str(len(self.rows)+1)
        self.rows.append([n,o,x,y]);self.cache[key]=n;return n
    def m(self,x,y,n=None):return self.op('*',x,y,n)
    def a(self,x,y,n=None):return self.op('+',x,y,n)
    def s(self,x,y,n=None):return self.op('-',x,y,n)
    def q(self,x,n=None):return self.m(x,x,n)

def build():
    C=Circuit();m,a,s,q=C.m,C.a,C.s,C.q
    qm1=m('beta','J','qm1');qq=a(qm1,1,'q');q2=q(qq,'q2');q3=m(q2,qq,'q3')
    omega=a('w',qq,'omega');X=m(omega,qq,'X');Y=m('s',q3,'Y');E=m(X,Y,'E')
    k=a('eta','zeta','k');kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c');av=a(E,Y,'a');H=a(m(4,av),3,'H');Delta=a(q(av),H,'Delta');c2=q(c,'c2')
    G=a(m(Delta,c2),1,'G');ac=m(av,c,'ac');b0=a(X,ac,'b0');qF=s(qq,'F','qF');Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk');Nt=s(a(m(a('K0',omega),Cw),qF),m('z',qm1),'Nt')
    I=m('i',c2,'I');I2=q(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q');d=s(Q,1,'d')
    v=m(c,'T','v');v2=q(v,'v2');b=a(c,m(R,D),'b')
    k3=m(q(k),k,'k3');u=a(m('i',k3),'T','u');M=m(k,q(u),'M')
    HM=m(H,M,'HM');L=a(HM,1,'L')
    ap2=a(av,2,'ap2');delta=s(m(ap2,c),ell,'delta');Mdelta=m(M,delta,'Mdelta')
    shift=a(a(b,Mdelta),m(v,m(ap2,I)),'shift');W=a(b0,m(H,a('t',shift)),'W')
    H2=q(H,'H2');n=m(q(HM),A,'n');dn=m(d,n,'dn');HQ=m(H2,Q,'HQ')
    HP=m(HQ,m(D,v2),'HP');HU=m(HQ,q(b),'HU');He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
    W2=q(W,'W2');L2G=m(q(L),G,'L2G');Tr=m(2,m(d,a(W2,L2G)),'Tr');Kr=m(d,s(W2,L2G),'Kr');Kn=q(Kr,'Kn')
    at=s(Tr,m(2,a(dn,He)),'at');bt=s(s(q(s(dn,He)),j),Kn,'bt')
    vb=s(m(16,m(dn,j)),m(at,a(m(at,Tr),m(2,bt))),'vb');ur=s(q(bt),m(q(at),Kn),'ur')
    term1=m(Kn,q(vb),'term1');term2=m(ur,s(m(Tr,vb),ur),'term2')
    N=s(term1,term2,'N');out=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
    return {'witnesses':VARIABLES,'fixed_numerals':PORTS,'coefficient_binding':'COEFFICIENT_BINDING.json','domain':'positive integers','source':C.rows,'output':out,'exact_degree':938,'norm_exact_degree':929,'operations':len(C.rows)}

def evaluate(packet,values,modulus=None):
    e=dict(values)
    for n,op,x,y in packet['source']:
        x=x if isinstance(x,int) else e[x];y=y if isinstance(y,int) else e[y]
        z=x+y if op=='+' else x-y if op=='-' else x*y
        e[n]=z%modulus if modulus else z
    return e

if __name__=='__main__':
    p=build();dest=Path(__file__).resolve().parent
    (dest/'positive12_majorant_product.json').write_text(json.dumps(p,indent=2)+'\n')
    system=dict(p);system.pop('output');system['source']=p['source'][:-5]
    system['comparisons']=[['Nk',1],['Nt',1],['term1','term2']]
    system['exact_degree']=929;system['operations']=len(system['source'])
    (dest/'positive12_majorant_system.json').write_text(json.dumps(system,indent=2)+'\n')
    print(json.dumps({'product_operations':p['operations'],'product_degree':938,'system_operations':system['operations'],'system_degree':929},indent=2))
