#!/usr/bin/env python3
"""Emit the division-free eleven-positive-variable root-transport circuit.

The weighted/adaptive Pell interface, three-root norm and rational Pell
descent are inherited. The new affine auxiliary-coordinate shift makes
the centered auxiliary root positive before transport positivity is known.
"""
import json
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF']
WITNESSES=['j','F','alpha','i','T','X','Y','n','eta','zeta','gamma']

class DAG:
    def __init__(self):
        self.rows=[]
        self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(row[0]==name for row in self.rows):
            raise ValueError('Duplicate register '+name)
        self.rows.append([name,op,x,y]); self.cache[key]=name
        return name
    def add(self,x,y,name=None): return self.gate('+',x,y,name)
    def sub(self,x,y,name=None): return self.gate('-',x,y,name)
    def mul(self,x,y,name=None): return self.gate('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed: needed.update((x,y))
        return [r for r in self.rows if r[0] in needed],needed

def build():
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(3,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3'); q2m=sub(q2,1,'q2m')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY')
    c=add(kY,'eta','c'); c2=sq(c,'c2')
    I=mul('i',c2,'I')
    a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,q2m),mul(add('MC',mul(q,'MF')),J),'R')
    Fa=add('F','alpha','Fa'); Rhat=None
    M=mul(q3,qm,'M')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    ellk=add(ell,k,'ellk'); Dtau=add(mul(ell,ellk),1,'Dtau')
    I2=sq(I,'I2'); fm=mul(Delta,I2,'fm'); Df=add(fm,1,'Df')
    Q=mul(Delta,fm,'Q'); delta=sub(Q,1,'delta')
    Told=add('T',Fa,'Told'); cT=mul(c,Told,'cT'); V=sub(mul(Df,sub(cT,R)),c,'V')
    fmajor=mul(add(a,2),I,'fmajor'); L=mul(k,Told,'L')
    W=add(mul(qm,L),1,'W')
    Zbar=sub(add(mul(M,add(add(add(add(ellk,'n'),L),V),fmajor)),mul(qm,'Y')),
             mul(mul(q3,W),Bt),'Zbar')
    r0=sub(sub(k,R),1,'r0')
    S=mul(4,mul(q,'Y'),'S'); U=mul(q,S,'U')
    shift=sub(add(mul(U,'gamma'),mul(S,'X')),r0,'shift')
    Dstar=add(mul(U,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(U),add(mul(Delta,c2),1)),'A1')
    M2=sq(M,'M2'); A=mul(M2,Dtau,'A'); Bf=mul(M2,Df,'Bf')
    Dnum=sub(mul(Q,sq(V)),1,'Dnum'); Cnum=mul(M2,Dnum,'Cnum')
    z2=sq(Zbar,'z2'); ABsum=add(A,Bf,'ABsum'); AB=mul(A,Bf,'AB')
    delta2=sq(delta,'delta2'); Tn=mul(delta2,AB,'Tn')
    Rn=mul(delta,Cnum,'Rn')
    Jn=sub(mul(delta,sub(z2,ABsum)),Cnum,'Jn')
    Ncenter=sub(sq(Jn),mul(4,add(Tn,mul(Rn,ABsum))),'Ncenter')
    normtail=mul(mul(mul(64,Tn),Rn),z2,'normtail')
    N8=sub(sq(Ncenter),normtail,'N8')
    out=add(add(N8,A1),mul(N8,A1),'P11')
    rows,needed=d.live([out]); core,_=d.live([N8,A1])
    if not set(WITNESSES+PORTS)<=needed: raise ValueError('Dead input')
    return {'name':'p11_positive_degree211','domain':'strictly positive integers',
      'witnesses':WITNESSES,'fixed_numerals':PORTS,'source':rows,
      'residuals':[N8,A1],'output':out,'operations':len(rows),
      'system_operations':len(core),
      'operation_breakdown':dict(Counter(r[1] for r in rows)),
      'exact_degree':211,'residual_degrees':[198,13],
      'coefficient_binding':'coefficients/ACTIVE_BINDING.json',
      'proof_status':'ordinary existence proof; inherited native compiler and K215 calibration; not an end-to-end formal certificate'}

def main():
    packet=build()
    (ROOT/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({k:v for k,v in packet.items() if k!='source'},indent=2))

if __name__=='__main__': main()
