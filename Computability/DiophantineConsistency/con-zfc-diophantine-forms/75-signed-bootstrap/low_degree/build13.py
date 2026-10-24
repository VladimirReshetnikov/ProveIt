#!/usr/bin/env python3
"""Thirteen positive unknowns by two ordered integral-root carriers.

New composition of the parent's transport carrier with the fourteen-variable
index/scale carrier. All fixed ports bind to the whole source58 compact tuple.
"""
import json
from pathlib import Path
from collections import Counter
from dag import DAG,PORTS
ROOT=Path(__file__).resolve().parent
VARS=['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']

def build():
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(3,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3'); q4=sq(q2,'q4'); q5=mul(q4,q,'q5')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
    a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    W=add(mul(qm,k),1,'W'); M=mul(q3,qm,'M')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    root0=sub(add(mul(M,add(add(ell,k),'r')),mul(qm,'Y')),mul(mul(q3,W),Bt),'root0')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    A0=sub(sq(root0),mul(sq(M),rad0),'A0')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    Kidx=mul(mul(4,q),'Y','Kidx'); Uidx=mul(q,Kidx,'Uidx')
    shift=sub(add(mul(Uidx,'gamma'),mul(Kidx,'X')),r0,'shift')
    Dstar=add(mul(Uidx,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(Uidx),add(mul(Delta,c2),1)),'A1')
    f2=sq('f','f2'); f2m=sub(f2,1,'f2m'); Kaux=mul(Delta,f2m,'Kaux'); I=mul('i',c2,'I')
    As=sub(f2m,mul(Delta,sq(I)),'As')
    V=sub(mul(f2,sub(mul(c,'T'),R)),c,'V')
    y2=sq(add(V,'u'),'y2')
    Aa=sub(sub(y2,mul(Kaux,sub(y2,sq(V)))),1,'Aa')
    residuals=[A0,A1,Aa,As]
    out=sq(residuals[0])
    for res in residuals[1:]: out=add(out,sq(res))
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(VARS+PORTS)<=needed: raise ValueError('Dead input')
    return {'name':'thirteen_positive_degree30','domain':'strictly positive integers','witnesses':VARS,'fixed_numerals':PORTS,'source':rows,'residuals':residuals,'output':out,'operations':len(rows),'system_operations':len(core),'operation_breakdown':dict(Counter(r[1] for r in rows)),'exact_degree':30,'residual_degrees':[15,13,13,14],'coefficient_binding':'whole source58/source44 compact tuple beta=2^590069-1; MF already shifted','proof_status':'new ordinary existence reduction; inherited compiler and Pell index theorem; no new Lean certificate'}

if __name__=='__main__':
    p=build(); (ROOT/'p13_degree30.json').write_text(json.dumps(p,indent=2)+'\n'); print(json.dumps({k:v for k,v in p.items() if k!='source'},indent=2))
