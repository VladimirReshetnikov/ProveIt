#!/usr/bin/env python3
"""Eleven positive unknowns: absorbed quotient with no inner separator.

The four ports are fixed integer coefficients from one bound K215 tuple.
Every binary +, -, * is charged; reuse is free. No upstream program imports.
"""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
VARIABLES = ['J','F','alpha','z','i','T','s','w','eta','zeta','t']
PORTS = ['beta','K0','MC','MF']

class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self, op, x, y, name=None):
        pair=tuple(sorted((x,y), key=str)) if op in ('+','*') else (x,y)
        key=(op,)+pair
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows)+1)
        self.rows.append([name,op,x,y]); self.cache[key]=name
        return name
    def add(self,x,y,name=None): return self.gate('+',x,y,name)
    def sub(self,x,y,name=None): return self.gate('-',x,y,name)
    def mul(self,x,y,name=None): return self.gate('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)

def build(presentation='product',carrier='full'):
    C=Circuit(); a,s,m,sq=C.add,C.sub,C.mul,C.sq
    qm1=m('beta','J','qm1'); q=a(qm1,1,'q'); q2=sq(q,'q2'); q3=m(q,q2,'q3')
    s0=a('s',m(3,q),'s0'); X=m('w',q,'X'); Y=m(s0,q3,'Y'); E=m(X,Y,'E')
    k=a('eta','zeta','k'); kY=m(k,Y,'kY'); ell=m(E,kY,'ell'); A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c'); aa=a(E,Y,'a'); ac=m(aa,c,'ac'); b0=a(X,ac,'b0')
    H=a(m(4,aa),3,'H'); Delta=a(sq(aa),H,'Delta'); c2=sq(c,'c2'); G=a(m(Delta,c2),1,'G')
    qF=s(q,'F','qF'); Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(q,'MF')),'J'),'R')
    transleft=m(a('K0','w'),Cw,'transleft'); zqm1=m('z',qm1,'zqm1')
    if presentation=='shifted_system': transright=a('F',zqm1,'transright'); Nt=None
    else: Nt=s(a(transleft,qF),zqm1,'Nt')
    I=m('i',c2,'I'); Dm1=m(Delta,sq(I),'Dm1'); D=a(Dm1,1,'D'); Q=m(Delta,Dm1,'Q'); d=s(Q,1,'d')
    v=m(c,'T','v'); v2=sq(v,'v2'); b=a(c,m(R,D),'b'); K=a(m(I,'T','IT'),1,'K')
    L0=a(m(H,K),1,'L0'); L=m(E,L0,'L'); S=m(E,H,'S'); S2=sq(S,'S2')
    if carrier=='full': delta=s(m(a(aa,2),c),ell,'delta')
    elif carrier=='short': delta=s(ac,ell,'delta')
    else: raise ValueError(carrier)
    offset=s(s(a(m(E,a('t',a(b,delta))),k),R),1,'offset')
    W=a(m(E,b0),m(H,offset),'W')
    dn=m(d,m(S2,A),'dn'); SQ=m(S2,Q,'SQ'); HP=m(SQ,m(D,v2),'HP'); HU=m(SQ,sq(b),'HU')
    He=s(a(HP,HU),S2,'He'); j=m(4,m(HP,HU),'j'); W2=sq(W,'W2'); L2G=m(sq(L),G,'L2G')
    Trace=m(2,m(d,a(W2,L2G)),'Trace'); Knorm=sq(m(d,s(W2,L2G)),'Knorm')
    AA=m(2,a(dn,He),'AA'); constant=s(sq(s(dn,He)),j,'constant'); at=s(Trace,AA,'at'); bt=s(constant,Knorm,'bt')
    coef=m(16,m(dn,j),'coef'); vbar=s(coef,m(at,a(m(at,Trace),m(2,bt))),'vbar')
    ur=s(sq(bt),m(sq(at),Knorm),'ur'); term1=m(ur,s(m(Trace,vbar),ur),'term1'); term2=m(Knorm,sq(vbar),'term2')
    deg={'full':988,'short':992}[carrier]
    p={'name':'eleven_'+carrier+'_'+presentation, 'domain':'strictly positive integers', 'witnesses':VARIABLES,
       'fixed_numerals':PORTS,'source':C.rows,'carrier':carrier,'presentation':presentation,
       'coefficient_binding':'../../coefficients/COEFFICIENT_BINDING.json',
       'construction_pin':'124c07c0b77a9e20e84676514d8b1ff78536ea3f',
       'proof_status':'Ordinary proof using inherited normalized K215 compiler; no new end-to-end formal certificate.'}
    if presentation in ('system','shifted_system'):
        p['comparisons']=[[transleft,transright] if presentation=='shifted_system' else [Nt,1],[term1,term2]]
        p['residual_exact_degrees']=[2,deg]; p['exact_degree']=deg
    else:
        N=s(term2,term1,'N')
        if presentation=='product': p['output']=s(m(Nt,a(N,1)),1,'polynomial'); p['exact_degree']=deg+2
        elif presentation=='sos': p['output']=a(sq(s(Nt,1)),sq(N),'polynomial'); p['exact_degree']=2*deg
        else: raise ValueError(presentation)
    return audit(p)

def audit(p):
    known=set(VARIABLES+PORTS); degrees={v:1 for v in VARIABLES}; degrees.update({v:0 for v in PORTS})
    for name,op,x,y in p['source']:
        if name in known or op not in ('+','-','*'): raise ValueError('invalid gate '+name)
        for v in (x,y):
            if isinstance(v,str) and v not in known: raise ValueError('unbound '+v)
        dx=0 if isinstance(x,int) else degrees[x]; dy=0 if isinstance(y,int) else degrees[y]
        degrees[name]=dx+dy if op=='*' else max(dx,dy); known.add(name)
    live=set([p['output']] if 'output' in p else [v for pair in p['comparisons'] for v in pair if isinstance(v,str)])
    for name,op,x,y in reversed(p['source']):
        if name not in live: raise ValueError('dead gate '+name)
        live.update(v for v in (x,y) if isinstance(v,str))
    if not set(VARIABLES+PORTS)<=live: raise ValueError('dead input')
    counts=Counter(r[1] for r in p['source'])
    p['ledger']={'operations':len(p['source']),'multiplications':counts['*'],'additions':counts['+'],'subtractions':counts['-'],'all_gates_and_inputs_live':True}
    p['syntactic_degree_bound']=degrees[p.get('output','term1')]
    return p

def evaluate(packet,values,modulus=None):
    env=dict(values)
    for name,op,x,y in packet['source']:
        x=x if isinstance(x,int) else env[x]; y=y if isinstance(y,int) else env[y]
        value=x+y if op=='+' else x-y if op=='-' else x*y
        env[name]=value if modulus is None else value%modulus
    return env

def main():
    out=HERE/'generated'; out.mkdir(exist_ok=True); summary=[]
    for carrier in ('full','short'):
        for presentation in ('product','system','shifted_system','sos'):
            p=build(presentation,carrier); (out/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            summary.append({k:p[k] for k in ('name','ledger','exact_degree','syntactic_degree_bound')})
    (out/'BUILD_RECEIPT.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
