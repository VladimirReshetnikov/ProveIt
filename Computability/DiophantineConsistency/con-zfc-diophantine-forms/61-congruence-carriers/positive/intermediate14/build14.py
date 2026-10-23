#!/usr/bin/env python3
"""A fourteen-positive-variable integral-root/index-absorption circuit.

The fixed coefficient tuple is the entire compact 590069-bit native tuple
of ProveIt source 44 / source 58. No individual port may be spliced.
All arithmetic gates are binary +, -, *. Intermediate names are registers.
"""
import json
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parent
VARS = ['j','F','alpha','z','f','i','T','X','Y','r','eta','zeta','u','gamma']
PORTS = ['beta','K0','MC','MF']

class DAG:
    def __init__(self): self.rows=[]; self.cache={}
    def g(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(r[0]==name for r in self.rows): raise ValueError(name)
        self.rows.append([name,op,x,y]); self.cache[key]=name; return name
    def add(self,x,y,name=None): return self.g('+',x,y,name)
    def sub(self,x,y,name=None): return self.g('-',x,y,name)
    def mul(self,x,y,name=None): return self.g('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed: needed.update((x,y))
        return [r for r in self.rows if r[0] in needed],needed

def build():
    d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(3,'j'),1,'J')
    qm=mul('beta',J,'qm'); q=add(qm,1,'q')
    q2=sq(q,'q2'); q3=mul(q2,q,'q3'); q4=sq(q2,'q4'); q5=mul(q4,q,'q5'); q6=sq(q3,'q6')
    qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
    E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
    a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
    root0=add(mul(q3,add(ell,'r')),'Y','root0')
    rad0=add(mul(ell,add(ell,k)),1,'rad0')
    A0=sub(sq(root0),mul(q6,rad0),'A0')
    G=add(mul(qm,qF),'alpha','G')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
    r0=sub(sub(k,R),1,'r0')
    shift=sub(add(mul(q5,'gamma'),mul(q4,'X')),r0,'shift')
    Dstar=add(mul(q5,b0),mul(H,shift),'Dstar')
    A1=sub(sq(Dstar),mul(sq(q5),add(mul(Delta,c2),1)),'A1')
    transport=sub(add(mul('K0',C),qF),mul('z',qm),'transport')
    At=sub(add(mul(q,transport),mul('X',C)),q,'At')
    f2=sq('f','f2'); Kaux=mul(Delta,sub(f2,1),'Kaux'); I=mul('i',c2,'I')
    As=sub(sub(f2,mul(Delta,sq(I))),1,'As')
    V=sub(mul(f2,sub(mul(c,'T'),R)),c,'V')
    Aa=sub(sub(sq(add(V,'u')),mul(Kaux,mul('u',add(mul(2,V),'u')))),1,'Aa')
    residuals=[A0,A1,At,Aa,As]
    out=sq(residuals[0]);
    for res in residuals[1:]: out=add(out,sq(res))
    rows,needed=d.live([out]); core,_=d.live(residuals)
    if not set(VARS+PORTS)<=needed: raise ValueError('dead input')
    return {'name':'fourteen_positive_degree34','domain':'strictly positive integers','witnesses':VARS,'fixed_numerals':PORTS,'source':rows,'residuals':residuals,'output':out,'operations':len(rows),'system_operations':len(core),'operation_breakdown':dict(Counter(r[1] for r in rows)),'exact_degree':34,'residual_degrees':[11,17,3,13,14],'coefficient_binding':'whole source58/source44 compact tuple beta=2^590069-1; MF already shifted','proof_status':'new ordinary existence reduction; inherited compiler and Pell index theorem; no new Lean certificate'}

if __name__=='__main__':
    p=build(); (ROOT/'p14_degree34.json').write_text(json.dumps(p,indent=2)+'\n'); print(json.dumps({k:v for k,v in p.items() if k not in ('source',)},indent=2))
