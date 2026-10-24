#!/usr/bin/env python3
"""Literal division-free circuits for the centered Pell-gap construction.

Only the Python standard library is required. Four named leaves are fixed
integers, loaded by evaluate.py from the complete compact44 binding.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PORTS = ['beta', 'K0', 'MC', 'MF']
VARS12 = ['j','F','alpha','i','T','X','Y','r','eta','zeta','n','gamma']

class DAG:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(row[0]==name for row in self.rows): raise ValueError(name)
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
        return [row for row in self.rows if row[0] in needed],needed

def build12(mode='product'):
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(6,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY')
    c=add(kY,'eta','c'); c2=sq(c,'c2'); a=add(E,'Y','a')
    H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    W=add(mul(qm,k),1,'W'); M0=mul(q3,qm,'M0')
    Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
    Z=sub(add(mul(M0,add(add(ell,k),'r')),mul(qm,'Y')),
          mul(mul(q3,W),Bt),'Z')
    A0=sub(sq(Z),mul(sq(M0),add(mul(ell,add(ell,k)),1)),'A0')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    L=mul(q,'Y','L'); U=mul(q,L,'U')
    shift=sub(add(mul(U,'gamma'),mul(L,'X')),r0,'shift')
    Dstar=add(mul(U,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(U),add(mul(Delta,c2),1)),'A1')
    I=mul('i',c2,'I'); I2=sq(I,'I2'); Dm=mul(Delta,I2,'Dm')
    D=add(Dm,1,'D'); Q=mul(Delta,Dm,'Q'); dd=sub(Q,1,'d')
    A=add(a,2,'A'); f0=mul(A,I,'f0')
    V=sub(mul(D,sub(mul(c,'T'),R)),c,'V')
    x=add(add('n',f0),V,'x')
    Eaux=sub(mul(Q,sq(V)),1,'Eaux')
    delta=sub(sq(x),D,'delta')
    Fnorm=sub(mul(dd,delta),Eaux,'Fnorm')
    N=sub(sq(Fnorm),mul(mul(mul(4,dd),D),Eaux),'N')
    residuals=[A0,A1,N]
    if mode=='product':
        out=sub(mul(mul(add(1,A0),add(1,A1)),add(1,N)),1,'P12')
    elif mode=='sos':
        out=add(add(sq(A0),sq(A1)),sq(N),'P12')
    else: raise ValueError(mode)
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(VARS12+PORTS)<=needed: raise ValueError('dead input')
    return dict(name='centered_gap_twelve_positive_'+mode,
                domain='strictly positive integers', witnesses=VARS12,
                fixed_numerals=PORTS,source=rows,residuals=residuals,output=out,
                operations=len(rows),system_operations=len(core),
                operation_breakdown=dict(Counter(row[1] for row in rows)),
                exact_degree=110 if mode=='product' else 164,
                residual_degrees=[15,13,82],
                coefficient_binding='../coefficients/COEFFICIENT_BINDING.json',
                source_snapshot='a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49',
                proof_status='ordinary mathematical reduction with explicit inherited compiler and Pell calibration; no new proof-assistant endpoint')

if __name__=='__main__':
    (ROOT/'circuits').mkdir(exist_ok=True)
    for mode in ['product','sos']:
        p=build12(mode)
        (ROOT/'circuits'/('positive12_'+mode+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        print(json.dumps({k:v for k,v in p.items() if k not in ['source','coefficient_binding','proof_status']}))
