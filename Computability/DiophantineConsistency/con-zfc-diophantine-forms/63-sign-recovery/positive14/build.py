#!/usr/bin/env python3
"""Fourteen-positive consistency polynomial: degree 34, explicit binary DAG."""
from pathlib import Path
import json
from collections import Counter

ROOT = Path(__file__).resolve().parent
VARIABLES = ['J','F','alpha','z','f','i','T','w','Y','r','eta','zeta','u','t']
PORTS = ['beta','K0','MC','MF']

class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self,op,a,b,name=None):
        pair=tuple(sorted((a,b),key=lambda x:(str(type(x)),str(x)))) if op in ('+','*') else (a,b)
        key=(op,*pair)
        if key in self.cache:return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(x[0]==name for x in self.rows):raise ValueError('repeated gate')
        self.rows.append([name,op,a,b]);self.cache[key]=name;return name
    def add(self,a,b,name=None):return self.gate('+',a,b,name)
    def sub(self,a,b,name=None):return self.gate('-',a,b,name)
    def mul(self,a,b,name=None):return self.gate('*',a,b,name)
    def sq(self,a,name=None):return self.mul(a,a,name)
    def finish(self,outputs):
        needed=set(outputs)
        for name,op,a,b in reversed(self.rows):
            if name in needed:needed.update((a,b))
        return [row for row in self.rows if row[0] in needed],needed

def build(certificate=False, shifted=True):
    d=Circuit(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    qm=mul('beta','J','qm');q=add(qm,1,'q');q2=sq(q,'q2');q3=mul(q2,q,'q3')
    q6=sq(q3,'q6');M=mul(4,sq(q2),'M')
    qF=sub(q,'F','qF');C=sub(qF,'alpha','C')
    X=mul('w',q,'X');E=mul(X,'Y','E');k=add('eta','zeta','k')
    kY=mul(k,'Y','kY');c=add(kY,'eta','c');c2=sq(c,'c2')
    a=add(E,'Y','a');H=add(mul(4,a),3,'H');Delta=add(sq(a),H,'Delta')
    ac=mul(a,c,'ac');b0=add(X,ac,'b0');ell=mul(E,kY,'ell')
    ellr=add(ell,'r','ell_r')
    if certificate:
        firstcore=sub(add(sq('r'),mul(ell,sub(mul(2,'r'),k))),1)
        A0=add(add(mul(q6,firstcore),mul(mul(2,q3),mul(ellr,'Y'))),sq('Y'),'A0')
    else:
        firstnum=add(mul(q3,ellr),'Y','first_num')
        firstbase=add(mul(ell,add(ell,k)),1,'first_base')
        A0=sub(sq(firstnum),mul(q6,firstbase),'A0')
    R=add(mul(add(mul(qm,qF),'alpha'),sub(q2,1)),mul(add('MC',mul(q,'MF')),'J'),'R')
    rindex=sub(sub(k,R),1,'index_gap');Z=sub(mul(M,'t'),rindex,'Z')
    W=add(mul(M,b0),mul(H,Z),'W')
    if certificate:
        defect=sub(sub(add(sq(X),mul(mul(2,ac),X)),mul(H,c2)),1,'defect')
        A1=add(add(mul(sq(M),defect),mul(mul(mul(2,M),b0),mul(H,Z))),sq(mul(H,Z)),'A1')
    else:
        A1=sub(sq(W),mul(sq(M),add(mul(Delta,c2),1)),'A1')
    if shifted:
        At=sub(sub(mul(add('K0','w'),C),'F'),mul('z',qm),'At')
    else:
        Nt=sub(add(mul(add('K0','w'),C),qF),mul('z',qm),'Nt')
        At=sub(Nt,1,'At')
    f2=sq('f','f2');fm=sub(f2,1,'fm');I=mul('i',c2,'I');Q=mul(Delta,fm,'Q')
    As=sub(fm,mul(Delta,sq(I)),'As')
    V=sub(mul(c,sub(mul('T','f'),1)),mul(R,f2),'V')
    Au=sub(sub(sq(add(V,'u')),mul(Q,mul('u',add(mul(2,V),'u')))),1,'Au')
    residuals=[A0,A1,At,As,Au]
    out=sq(residuals[0])
    for value in residuals[1:]:out=add(out,sq(value))
    rows,needed=d.finish([out]);core,_=d.finish(residuals)
    if not set(VARIABLES+PORTS)<=needed:raise ValueError('dead input')
    return {'name':'pell14_degree34','domain':'strictly positive integers','variables':VARIABLES,
        'fixed_numerals':PORTS,'source':rows,'residuals':residuals,'output':out,'exact_degree':34,
        'transport_coordinate':'z=old_z-1' if shifted else 'z=old_z',
        'coefficient_binding':'../coefficients/payloads/COEFFICIENT_BINDING.json',
        'coefficient_aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
        'fixed_tuple':'mixed-parity-unrounded-1064921; all four ports together; MF already shifted',
        'proof':'PROOF.md',
        'operations':len(rows),'operation_breakdown':dict(Counter(x[1] for x in rows)),
        'residual_operations':len(core),'degree_certificate_only':certificate}

def main():
    for cert in (False,True):
        p=build(cert);fn='pell14_degree34'+('_degree_certificate' if cert else '')+'.json'
        (ROOT/fn).write_text(json.dumps(p,indent=2)+'\n')
        print(fn,p['operations'],p['operation_breakdown'],p['residual_operations'])
    p=build(False,False)
    (ROOT/'pell14_degree34_unshifted.json').write_text(json.dumps(p,indent=2)+'\n')
    print('unshifted',p['operations'],p['operation_breakdown'])
    p=build(); p['name']='pell14_natural_degree34'
    p['domain']='nonnegative integers'
    rename={v:'positive_'+v for v in VARIABLES}
    prefix=[[rename[v],'+',v,1] for v in VARIABLES]
    p['source']=prefix+[[n,op,rename.get(a,a),rename.get(b,b)] for n,op,a,b in p['source']]
    p['operations']=len(p['source']);p['residual_operations']+=len(VARIABLES)
    p['operation_breakdown']=dict(Counter(row[1] for row in p['source']))
    p['domain_translation']='Each listed input is replaced by input+1 in the positive polynomial.'
    (ROOT/'pell14_natural_degree34.json').write_text(json.dumps(p,indent=2)+'\n')
    print('natural',p['operations'],p['operation_breakdown'])
if __name__=='__main__':main()
