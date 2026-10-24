#!/usr/bin/env python3
"""Build the explicit twelve-positive-variable degree-78 equation.

The two carriers are the exact package61 formulas, with J=6j+1.
The saturated Pell norm merger is the new part. Standard library only.
"""
import json
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF']
VARS=['j','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']

class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache:return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(row[0]==name for row in self.rows):raise ValueError(name)
        self.rows.append([name,op,x,y]);self.cache[key]=name
        return name
    def add(self,x,y,name=None):return self.gate('+',x,y,name)
    def sub(self,x,y,name=None):return self.gate('-',x,y,name)
    def mul(self,x,y,name=None):return self.gate('*',x,y,name)
    def sq(self,x,name=None):return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed:needed.update((x,y))
        return [row for row in self.rows if row[0] in needed],needed

def build():
    d=Circuit();add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(6,'j'),1,'J');qm=mul('beta',J,'qm');q=add(qm,1,'q')
    q2=sq(q,'q2');q3=mul(q2,q,'q3');S=mul(4,mul(q,'Y'),'S');U=mul(q,S,'U')
    qF=sub(q,'F','qF');C=sub(qF,'alpha','C')
    E=mul('X','Y','E');k=add('eta','zeta','k');kY=mul(k,'Y','kY');c=add(kY,'eta','c');c2=sq(c,'c2')
    a=add(E,'Y','a');H=add(mul(4,a),3,'H');Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac');b0=add('X',ac,'b0');ell=mul(E,kY,'ell')
    W=add(mul(qm,k),1,'W');M=mul(q3,qm,'M')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    root0=sub(add(mul(M,add(add(ell,k),'r')),mul(qm,'Y')),mul(mul(q3,W),Bt),'root0')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    A0=sub(sq(root0),mul(sq(M),rad0),'A0')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    shift=sub(add(mul(U,'gamma'),mul(S,'X')),r0,'shift')
    Dstar=add(mul(U,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(U),add(mul(Delta,c2),1)),'A1')
    f=add('t',1,'f');f2=sq(f,'f2');rho=sub(f2,1,'rho')
    Q=mul(Delta,rho,'Q');oneQ=sub(1,Q,'oneQ');den=mul(Delta,sq(c2),'den')
    V=sub(mul(f2,sub(mul(c,'T'),R)),c,'V')
    # h(n)=(V+n)²-Q[(V+n)²-V²]-1. Share the existing root sum.
    vn=add(V,'n','vn');vn2=sq(vn,'vn2')
    aux_a=sub(sub(vn2,mul(Q,sub(vn2,sq(V)))),1,'aux_a')
    aux_b=mul(mul(2,oneQ),vn,'aux_b')
    normA=add(mul(den,aux_a),mul(oneQ,rho),'normA')
    N=sub(sq(normA),mul(mul(den,rho),sq(aux_b)),'N')
    out=sub(mul(mul(add(A0,1),add(A1,1)),add(N,1)),1,'P12')
    rows,needed=d.live([out]);core,_=d.live([A0,A1,N])
    if not set(VARS+PORTS)<=needed:raise ValueError('Dead input or port')
    return {'name':'twelve_positive_pell_saturation_degree78','domain':'strictly positive integers','witnesses':VARS,'fixed_numerals':PORTS,'source':rows,'residuals':[A0,A1,N],'output':out,'operations':len(rows),'system_operations':len(core),'operation_breakdown':dict(Counter(row[1] for row in rows)),'exact_degree':78,'residual_degrees':[15,13,50],'coefficient_binding':'../coefficients/ACTIVE_BINDING.json','proof_status':'Ordinary mathematical reduction with exact finite certificates; inherited package61 compiler/refutation calibration; no new end-to-end Lean/Rocq certificate.'}

if __name__=='__main__':
    obj=build();(ROOT/'equation.json').write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps({k:v for k,v in obj.items() if k!='source'},indent=2))
