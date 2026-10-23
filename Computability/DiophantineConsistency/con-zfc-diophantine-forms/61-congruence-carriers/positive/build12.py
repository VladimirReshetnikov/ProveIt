#!/usr/bin/env python3
"""Construct two twelve-positive-variable equations using a divided Pell norm."""
import json
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parent
VARS = ['j','F','alpha','i','T','X','Y','r','eta','zeta','n','gamma']
PORTS = ['beta','K0','MC','MF']

class DAG:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(a[0]==name for a in self.rows): raise ValueError(name)
        self.rows.append([name,op,x,y]); self.cache[key]=name; return name
    def add(self,x,y,name=None): return self.gate('+',x,y,name)
    def sub(self,x,y,name=None): return self.gate('-',x,y,name)
    def mul(self,x,y,name=None): return self.gate('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed: needed.update((x,y))
        return [row for row in self.rows if row[0] in needed],needed

def build(mode='product', split=2):
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(6,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3'); q4=sq(q2,'q4'); q5=mul(q4,q,'q5')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
    a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    W=add(mul(qm,k),1,'W'); M0=mul(q3,qm,'M0')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    Z=sub(add(mul(M0,add(add(ell,k),'r')),mul(qm,'Y')),mul(mul(q3,W),Bt),'Z')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    A0=sub(sq(Z),mul(sq(M0),rad0),'A0')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    shift=sub(add(mul(q5,'gamma'),mul(q4,'X')),r0,'shift')
    Dstar=add(mul(q5,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(q5),add(mul(Delta,c2),1)),'A1')
    ic=mul('i',c,'ic'); D=add(mul(mul(Delta,c2),sq(ic)),1,'D')
    if split==0:
        Mbase=sq(mul(Delta,'i'),'Mbase')
        M=Mbase; Caux=sq(c2,'Caux')
    elif split==1:
        Mbase=sq(mul(Delta,'i'),'Mbase')
        M=mul(Mbase,c,'Maux'); Caux=mul(c2,c,'Caux')
    elif split==2:
        Caux=mul(Delta,ic,'Caux'); M=mul(Caux,c2,'Maux')
    else: raise ValueError('split must be 0, 1 or 2')
    Q=mul(M,Caux,'Q'); dd=sub(Q,1,'dd')
    V=sub(mul(D,sub(mul(c,'T'),R)),c,'V')
    Mn=mul(M,'n','Mn')
    normA=add(sub(mul(mul(dd,M),add(sq('n'),D)),mul(mul(2,dd),'n')),mul(Caux,sub(1,sq(V))),'normA')
    normB=mul(mul(2,dd),sub(Mn,1),'normB')
    N=sub(sq(normA),mul(sq(normB),D),'N')
    residuals=[A0,A1,N]
    if mode=='product':
        out=sub(mul(mul(add(1,A0),add(1,A1)),add(1,N)),1,'P12')
    elif mode=='sos':
        out=add(add(sq(A0),sq(A1)),sq(N),'P12')
    else: raise ValueError(mode)
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(VARS+PORTS)<=needed: raise ValueError('dead input')
    norm_degree=86 if split==2 else 88
    return dict(name='twelve_positive_'+mode+'_split'+str(split)+'',domain='strictly positive integers',witnesses=VARS,fixed_numerals=PORTS,source=rows,residuals=residuals,output=out,operations=len(rows),system_operations=len(core),operation_breakdown=dict(Counter(row[1] for row in rows)),exact_degree=32+norm_degree if mode=='product' else 2*norm_degree,residual_degrees=[15,17,norm_degree],coefficient_binding='whole source44 compact tuple beta=2^590069-1; MF is already shifted',proof_status='ordinary mathematical existence reduction with named inherited compiler and Pell dependencies; no new end-to-end proof assistant certificate')

if __name__=='__main__':
    for mode,split in [('product',2),('sos',2)]:
        packet=build(mode,split)
        path=ROOT/('p12_'+mode+'_split'+str(split)+'.json')
        path.write_text(json.dumps(packet,indent=2)+'\n')
        print(json.dumps({k:v for k,v in packet.items() if k!='source'}))
