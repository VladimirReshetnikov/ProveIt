#!/usr/bin/env python3
"""New division-free degree-901 positive carrier; no upstream program imports."""
import json,gzip,hashlib
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
VARIABLES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']
def verify_binding():
    binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text());values={}
    for item in binding['payloads']:
        packed=(HERE/item['path']).read_bytes();raw=gzip.decompress(packed)
        if hashlib.sha256(packed).hexdigest()!=item['gzip_sha256']:raise ValueError('gzip hash '+item['name'])
        if hashlib.sha256(raw).hexdigest()!=item['sha256']:raise ValueError('payload hash '+item['name'])
        value=int.from_bytes(raw,'little')
        if len(raw)!=item['bytes'] or value.bit_length()!=item['bit_length']:raise ValueError('payload size '+item['name'])
        values[item['name']]=value
    return {port:values[name] for port,name in binding['port_aliases'].items()}
class Circuit:
    def __init__(self): self.rows=[]
    def gate(self,op,x,y,name=None):
        name=name or 'g'+str(len(self.rows)+1)
        self.rows.append([name,op,x,y]);return name
    def add(self,x,y,name=None): return self.gate('+',x,y,name)
    def sub(self,x,y,name=None): return self.gate('-',x,y,name)
    def mul(self,x,y,name=None): return self.gate('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
def build(carrier='full',presentation='product'):
    C=Circuit();a,s,m,q=C.add,C.sub,C.mul,C.sq
    qm1=m('beta','J','qm1');qq=a(qm1,1,'q');q2=q(qq,'q2');q3=m(qq,q2,'q3')
    X=m('w',qq,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k')
    kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c');aa=a(E,Y,'a');ac=m(aa,c,'ac');b0=a(X,ac,'b0')
    H=a(m(4,aa),3,'H');H2=q(H,'H2');Delta=a(q(aa),H,'Delta')
    c2=q(c,'c2');G=a(m(Delta,c2),1,'G');qF=s(qq,'F','qF');Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk');transleft=m(a('K0','w'),Cw,'transleft')
    if presentation=='shifted_system':
        transright=a('F',m('z',qm1),'transright');Nt=None
    else: Nt=s(a(transleft,qF),m('z',qm1),'Nt')
    I=m('i',c2,'I');I2=q(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q')
    d=s(Q,1,'d');v=m(c,'T','v');v2=q(v,'v2');b=a(c,m(R,D),'b')
    K=a(m(I,'T','IT'),1,'K');L=a(m(H,K),1,'L')
    if carrier=='full': delta=s(m(a(aa,2),c),ell,'delta')
    elif carrier=='short': delta=s(ac,ell,'delta')
    else: raise ValueError(carrier)
    W=a(b0,m(H,a('t',a(b,delta))),'W')
    dn=m(d,m(H2,A),'dn');HQ=m(H2,Q,'HQ')
    HP=m(HQ,m(D,v2),'HP');HU=m(HQ,q(b),'HU');He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
    W2=q(W,'W2');L2G=m(q(L),G,'L2G');Trace=m(2,m(d,a(W2,L2G)),'Trace')
    Knorm=q(m(d,s(W2,L2G)),'Knorm');AA=m(2,a(dn,He),'AA')
    constant=s(q(s(dn,He)),j,'constant');at=s(Trace,AA,'at');bt=s(constant,Knorm,'bt')
    coef=m(16,m(dn,j),'coef');vbar=s(coef,m(at,a(m(at,Trace),m(2,bt))),'vbar')
    ur=s(q(bt),m(q(at),Knorm),'ur');term1=m(ur,s(m(Trace,vbar),ur),'term1');term2=m(Knorm,q(vbar),'term2')
    p={'name':carrier+'_'+presentation,'domain':'strictly positive integers','witnesses':VARIABLES,'fixed_numerals':PORTS,'source':C.rows,'carrier':carrier,'presentation':presentation,'coefficient_binding':'COEFFICIENT_BINDING.json','proof':'PROOF.md'}
    degree={'full':892,'short':896}[carrier]
    if presentation in ['system','shifted_system']:
        p['comparisons']=[[Nk,1],[transleft,transright] if presentation=='shifted_system' else [Nt,1],[term1,term2]]
        p['residual_exact_degrees']=[7,2,degree];p['exact_degree']=degree
    else:
        N=s(term2,term1,'N')
        if presentation=='product': p['output']=s(m(m(Nk,Nt),a(N,1)),1,'polynomial');p['exact_degree']=degree+9
        elif presentation=='sos':p['output']=a(a(q(s(Nk,1)),q(s(Nt,1))),q(N),'sos');p['exact_degree']=2*degree
        else: raise ValueError(presentation)
    return audit(p)
def audit(p):
    names=set(VARIABLES+PORTS);degrees={x:1 for x in VARIABLES};degrees.update({x:0 for x in PORTS})
    for n,op,x,y in p['source']:
        if n in names:raise ValueError('duplicate '+n)
        for v in [x,y]:
            if isinstance(v,str) and v not in names:raise ValueError('unbound '+v)
        dx=0 if isinstance(x,int) else degrees[x];dy=0 if isinstance(y,int) else degrees[y]
        degrees[n]=dx+dy if op=='*' else max(dx,dy);names.add(n)
    live=set([p['output']] if 'output' in p else [v for row in p['comparisons'] for v in row if isinstance(v,str)])
    for n,op,x,y in reversed(p['source']):
        if n not in live:raise ValueError('dead gate '+n)
        live.update(v for v in [x,y] if isinstance(v,str))
    if not set(VARIABLES+PORTS)<=live:raise ValueError('dead input')
    count=Counter(r[1] for r in p['source'])
    p['ledger']={'operations':len(p['source']),'multiplications':count['*'],'additions_subtractions':count['+']+count['-'],'all_gates_live':True,'all_ports_live':True}
    p['syntactic_degree_bound']=degrees[p.get('output','term1')]
    return p
def main():
    verify_binding();summary=[]
    for car in ['short','full']:
        for pres in ['product','system','shifted_system','sos']:
            p=build(car,pres);(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            summary.append({k:p[k] for k in ['name','ledger','exact_degree','syntactic_degree_bound']})
    (HERE/'BUILD_RECEIPT.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
