#!/usr/bin/env python3
"""Literal division-free circuits for the adaptive and root-transfer equations.

Shared-prefix arithmetic is adapted from ProveIt package 61 build13.py at
9cca523d9f27ad39d52993f4065cbd7e58f8bdd4 (MIT No Attribution).
The adaptive carrier uses package 65; the strong-root transfer is new here.
"""
import json
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parent
PORTS = ['beta', 'K0', 'MC', 'MF']

class DAG:
    def __init__(self):
        self.rows = []
        self.cache = {}
    def gate(self, op, x, y, name=None):
        if op in ('+', '*') and str(x) > str(y):
            x, y = y, x
        key = (op, x, y)
        if key in self.cache:
            return self.cache[key]
        name = name or 'g' + str(len(self.rows))
        if any(row[0] == name for row in self.rows):
            raise ValueError('Duplicate gate: ' + name)
        self.rows.append([name, op, x, y])
        self.cache[key] = name
        return name
    def add(self,x,y,name=None): return self.gate('+',x,y,name)
    def sub(self,x,y,name=None): return self.gate('-',x,y,name)
    def mul(self,x,y,name=None): return self.gate('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed: needed.update((x,y))
        return [row for row in self.rows if row[0] in needed],needed

def build(kind):
    if kind not in (12,13): raise ValueError(kind)
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    vars13=['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
    vars12=['j','F','alpha','i','T','X','Y','n','eta','zeta','u','gamma']
    names=vars13 if kind==13 else vars12
    J=add(mul(3,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY')
    c=add(kY,'eta','c'); c2=sq(c,'c2'); I=mul('i',c2,'I')
    a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    ikc=mul(mul('i',k),c,'ikc') if kind==12 else None
    weight=ikc if kind==12 else k
    W=add(mul(qm,weight),1,'W'); M=mul(q3,qm,'M')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    rr='r' if kind==13 else 'n'
    Z0=sub(add(mul(M,add(add(ell,k),rr)),mul(qm,'Y')),mul(mul(q3,W),Bt),'Z0')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    M2=sq(M,'M2')
    if kind==13:
        A0=sub(sq(Z0),mul(M2,rad0),'A0')
        f2=sq('f','f2'); f2m=sub(f2,1,'f2m'); I2=sq(I,'I2')
    else:
        I2=sq(I,'I2'); f2m=mul(Delta,I2,'f2m'); f2=add(f2m,1,'Df')
        L=mul(add(a,2),I,'L'); Zbar=add(Z0,mul(M,L),'Zbar')
        center=sub(sq(Zbar),mul(M2,add(f2,rad0)),'center')
        normtail=mul(mul(mul(4,sq(M2)),f2),rad0,'normtail')
        N=sub(sq(center),normtail,'N')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    S=mul(4,mul(q,'Y'),'S'); U=mul(q,S,'U')
    shift=sub(add(mul(U,'gamma'),mul(S,'X')),r0,'shift')
    Dstar=add(mul(U,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(U),add(mul(Delta,c2),1)),'A1')
    Kaux=mul(Delta,f2m,'Kaux')
    V=sub(mul(f2,sub(mul(c,'T'),R)),c,'V')
    y2=sq(add(V,'u'),'y2')
    Aa=sub(sub(y2,mul(Kaux,sub(y2,sq(V)))),1,'Aa')
    if kind==13:
        As=sub(f2m,mul(Delta,I2),'As')
        residuals=[A0,A1,Aa,As]; degrees=[15,13,13,14]
    else:
        residuals=[N,A1,Aa]; degrees=[42,13,37]
    out=sq(residuals[0])
    for r in residuals[1:]: out=add(out,sq(r))
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(names+PORTS)<=needed: raise ValueError('Dead input')
    return {'name':f'p{kind}_positive_degree{max(degrees)*2}',
      'domain':'strictly positive integers','witnesses':names,
      'fixed_numerals':PORTS,'source':rows,'residuals':residuals,'output':out,
      'operations':len(rows),'system_operations':len(core),
      'operation_breakdown':dict(Counter(r[1] for r in rows)),
      'exact_degree':max(degrees)*2,'residual_degrees':degrees,
      'coefficient_binding':'coefficients/ACTIVE_BINDING.json',
      'proof_status':'ordinary existence proof; inherited compact native compiler and K215 calibration; no new end-to-end formal certificate'}

def main():
    for kind in (13,12):
        packet=build(kind)
        path=ROOT/(packet['name']+'.json')
        path.write_text(json.dumps(packet,indent=2)+'\n')
        print(json.dumps({k:v for k,v in packet.items() if k!='source'},indent=2))
if __name__=='__main__': main()
