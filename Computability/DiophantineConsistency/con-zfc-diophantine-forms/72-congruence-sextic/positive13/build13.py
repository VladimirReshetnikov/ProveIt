#!/usr/bin/env python3
"""An explicit integer circuit for the positive-coordinate congruence carrier.

Fixed coefficient construction is separate from arithmetic on the 13 witnesses.
Only the four native ports beta, K0, MC, MF are independent fixed data.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
VARS = ['F','alpha','C','f0','i','T','X','Y','r','eta','zeta','u','gamma']
PORTS = ['beta','K0','MC','MF']
FIXED = {'B':['+', 'beta',1], 'b':['*',3,'beta'],
         'b2':['*','b','b'], 'L':['*','beta','b2'],
         'Kfinal':['*','b2',['*','L','L']], 'four_beta':['*',4,'beta']}

class DAG:
    def __init__(self):
        self.rows=[]; self.cache={}
    def gate(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(r[0]==name for r in self.rows): raise ValueError(name)
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
    qF=add('alpha','C','qF'); q=add('F',qF,'q'); qm=sub(q,1,'qm')
    q2=sq(q,'q2'); q3=mul(q,q2,'q3')
    k=add('eta','zeta','k'); kY=mul(k,'Y','kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
    E=mul('X','Y','E'); a=add(E,'Y','a'); H=add(mul(4,a),3,'H')
    Delta=add(sq(a),H,'Delta'); ell=mul(E,kY,'ell'); ac=mul(a,c,'ac'); b0=add('X',ac,'b0')
    nF=add(mul('b','f0'),sub(q,'B'),'nF'); f2=sq(nF,'f2'); f2m=sub(f2,'b2','f2m')
    I=mul('i',c2,'I'); As=sub(f2m,mul('b2',mul(Delta,sq(I))),'As')
    G=add(mul(qm,qF),'alpha','G')
    Rhat=add(mul('beta',mul(G,sub(q2,1))),mul(add('MC',mul(q,'MF')),qm),'Rhat')
    M0=mul(q3,qm,'M0'); Bt=sub(mul(add(mul(q,'K0'),'X'),'C'),mul(q,'F'),'Bt')
    Z=sub(add(mul(M0,add(ell,'r')),mul(qm,'Y')),mul(q3,Bt),'Z')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    A0=sub(sq(Z),mul(sq(M0),rad0),'A0')
    Sb=mul('four_beta',mul(q,'Y'),'Sb'); Mb=mul(q,Sb,'Mb')
    shift=add(sub(add(mul(Mb,'gamma'),mul(Sb,'X')),mul('beta',sub(k,1))),Rhat,'shift')
    Dhat=add(mul(Mb,b0),mul(H,shift),'Dhat')
    A1=sub(sq(Dhat),mul(sq(Mb),add(mul(Delta,c2),1)),'A1')
    Vhat=sub(mul(f2,sub(mul(mul('beta',c),'T'),Rhat)),mul('L',c),'Vhat')
    yhat=add(Vhat,mul('L','u'),'yhat'); yhat2=sq(yhat,'yhat2')
    Aa=sub(sub(mul('b2',yhat2),mul(mul(Delta,f2m),sub(yhat2,sq(Vhat)))),'Kfinal','Aa')
    residuals=[A0,A1,Aa,As]
    out=sq(A0)
    for res in residuals[1:]: out=add(out,sq(res))
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(VARS+PORTS)<=needed: raise ValueError('Dead input')
    return {'name':'positive_coordinate_congruence_13_degree28',
      'domain':'strictly positive integers','witnesses':VARS,'fixed_ports':PORTS,
      'derived_fixed_leaves':FIXED,'source':rows,'residuals':residuals,'output':out,
      'operations':len(rows),'system_operations':len(core),
      'operation_breakdown':dict(Counter(r[1] for r in rows)),
      'residual_degrees':[13,13,13,14],'exact_degree':28,
      'leading_form':'81*beta^4*i^4*(eta+zeta)^8*X^4*Y^12',
      'coefficient_binding':'Whole package44 compact tuple beta=2^590069-1; MF already shifted',
      'proof_status':'ordinary new reduction with inherited native compiler and Pell rank interfaces'}

def main():
    packet=build()
    (ROOT/'p13_degree28.json').write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({k:v for k,v in packet.items() if k not in ('source','derived_fixed_leaves')},indent=2))

if __name__=='__main__': main()
