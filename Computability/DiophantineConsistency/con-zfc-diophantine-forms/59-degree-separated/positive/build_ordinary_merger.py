#!/usr/bin/env python3
"""New ordinary-strong merger. Received programs are never imported."""
import json, gzip, hashlib
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
VARIABLES=['J','F','alpha','z','f0','T','s','w','eta','zeta','gamma','t']
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
    def __init__(self):self.rows=[]
    def gate(self,op,x,y,name=None):
        name=name or 'g'+str(len(self.rows)+1);self.rows.append([name,op,x,y]);return name
    def add(self,x,y,name=None):return self.gate('+',x,y,name)
    def sub(self,x,y,name=None):return self.gate('-',x,y,name)
    def mul(self,x,y,name=None):return self.gate('*',x,y,name)
    def sq(self,x,name=None):return self.mul(x,x,name)
def build(presentation='product'):
    C=Circuit();a,s,m,sq=C.add,C.sub,C.mul,C.sq
    qm1=m('beta','J','qm1');q=a(qm1,1,'q');q2=sq(q,'q2');q3=m(q2,q,'q3');q4=sq(q2,'q4');U=m(4,q4,'U')
    X=m('w',q,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k');kY=m(k,Y,'kY');c=a(kY,'eta','c')
    aa=a(E,Y,'a');H=a(m(4,aa),3,'H');Delta=a(sq(aa),H,'Delta');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
    c2=sq(c,'c2');c4=sq(c2,'c4');G=a(m(Delta,c2),1,'G');b0=a(X,m(aa,c),'b0')
    qF=s(q,'F','qF');Cw=s(qF,'alpha','Cw');R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(q,'MF')),'J'),'R')
    transleft=m(a('K0','w'),Cw,'transleft')
    if presentation=='shifted_system':transright=a('F',m('z',qm1),'transright')
    else:Nt=s(a(transleft,qF),m('z',qm1),'Nt')
    u=s(s(k,R),1,'u');Dstar=a(m(U,b0),m(H,s(m(U,'gamma'),u)),'Dstar');mainleft=sq(Dstar,'mainleft');mainright=m(sq(U),G,'mainright')
    f=a('f0',1,'f');f2=sq(f,'f2');Q=m(Delta,s(f2,1),'Q');d=s(Q,1,'d')
    V=s(m(c,s(m('T',f),1)),m(R,f2),'V');Eaux=s(m(Q,sq(V)),1,'Eaux')
    cf4=m(c4,f2,'cf4');Z=m(4,m(m(cf4,sq(ell)),Eaux),'Z')
    x=m(c2,'t','x');x2=sq(x,'x2');r=m(cf4,A,'r');p=Q
    M=s(m(d,a(a(x2,p),r)),Z,'M')
    d2=sq(d,'d2');pr=m(p,r,'pr');C0=a(sq(M),m(4,m(d2,s(m(x2,s(r,p)),pr))),'C0')
    B=s(m(2,m(d,p)),M,'B');innerleft=sq(C0,'innerleft');innerright=m(16,m(m(m(d2,x2),r),sq(B)),'innerright')
    out={'name':'ordinary_merger_'+presentation,'domain':'strictly positive integers','witnesses':VARIABLES,'fixed_numerals':PORTS,'source':C.rows,'presentation':presentation,'coefficient_binding':'COEFFICIENT_BINDING.json','proof':'PROOF.md'}
    if presentation in ['system','shifted_system']:
        out['comparisons']=[[transleft,transright] if presentation=='shifted_system' else [Nt,1],[mainleft,mainright],[innerleft,innerright]]
        out['residual_exact_degrees']=[2,26,288];out['exact_degree']=288
    else:
        main=s(mainleft,mainright,'Nmain');inner=s(innerleft,innerright,'Ninner')
        if presentation=='product':out['output']=s(m(m(Nt,a(main,1)),a(inner,1)),1,'polynomial');out['exact_degree']=316
        elif presentation=='sos':out['output']=a(a(sq(s(Nt,1)),sq(main)),sq(inner),'polynomial');out['exact_degree']=576
        else:raise ValueError(presentation)
    return audit(out)
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
    p['syntactic_degree_bound']=degrees[p.get('output','innerleft')];return p
def main():
    verify_binding();rows=[]
    for pres in ['product','system','shifted_system','sos']:
        p=build(pres);(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n');rows.append({k:p[k] for k in ['name','ledger','exact_degree','syntactic_degree_bound']})
    (HERE/'BUILD_RECEIPT.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
